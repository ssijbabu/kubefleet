/*
Copyright 2026 The KubeFleet Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package webhook

import (
	"bytes"
	"context"
	"crypto"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/rsa"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"errors"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/google/go-cmp/cmp"
	"github.com/prometheus/client_golang/prometheus/testutil"
	"github.com/sigstore/sigstore/pkg/signature/kms/fake"
	clocktesting "k8s.io/utils/clock/testing"

	"github.com/kubefleet-dev/kubefleet/cmd/hubagent/options"
	hubmetrics "github.com/kubefleet-dev/kubefleet/pkg/metrics/hub"
)

var testNow = time.Date(2026, time.September, 1, 0, 0, 0, 0, time.UTC)

// testCA is a CA certificate with its in-memory private key, standing in for a KMS-held key.
type testCA struct {
	key     crypto.Signer
	cert    *x509.Certificate
	certPEM []byte
}

func newTestCA(t *testing.T, commonName string, isCA bool, keyUsage x509.KeyUsage, notAfter time.Time) testCA {
	t.Helper()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatalf("ecdsa.GenerateKey() = %v, want no error", err)
	}
	return newTestCAWithKey(t, key, commonName, isCA, keyUsage, notAfter)
}

func newTestCAWithKey(t *testing.T, key crypto.Signer, commonName string, isCA bool, keyUsage x509.KeyUsage, notAfter time.Time) testCA {
	t.Helper()
	template := &x509.Certificate{
		SerialNumber:          big.NewInt(1),
		Subject:               pkix.Name{CommonName: commonName},
		NotBefore:             testNow.Add(-time.Hour),
		NotAfter:              notAfter,
		IsCA:                  isCA,
		BasicConstraintsValid: true,
		KeyUsage:              keyUsage,
	}
	der, err := x509.CreateCertificate(rand.Reader, template, template, key.Public(), key)
	if err != nil {
		t.Fatalf("x509.CreateCertificate() = %v, want no error", err)
	}
	cert, err := x509.ParseCertificate(der)
	if err != nil {
		t.Fatalf("x509.ParseCertificate() = %v, want no error", err)
	}
	return testCA{
		key:     key,
		cert:    cert,
		certPEM: pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der}),
	}
}

func newValidTestCA(t *testing.T) testCA {
	return newTestCA(t, "test-ca", true, x509.KeyUsageCertSign|x509.KeyUsageCRLSign, testNow.AddDate(1, 0, 0))
}

func TestNewExternalCA(t *testing.T) {
	validCA := newValidTestCA(t)
	otherCA := newTestCA(t, "other-ca", true, x509.KeyUsageCertSign, testNow.AddDate(1, 0, 0))
	notCA := newTestCA(t, "not-a-ca", false, x509.KeyUsageDigitalSignature, testNow.AddDate(1, 0, 0))
	noCertSignCA := newTestCA(t, "no-cert-sign", true, x509.KeyUsageDigitalSignature, testNow.AddDate(1, 0, 0))

	testCases := map[string]struct {
		caPEM               []byte
		signer              crypto.Signer
		servingCertValidity time.Duration
		wantIssuerName      string
		wantValidity        time.Duration
		wantErr             string
	}{
		"single CA certificate matching the key, default validity": {
			caPEM:          validCA.certPEM,
			signer:         validCA.key,
			wantIssuerName: "test-ca",
			wantValidity:   options.DefaultServingCertValidity,
		},
		"CA bundle during a rotation, the second certificate matches the key": {
			caPEM:          append(append([]byte{}, otherCA.certPEM...), validCA.certPEM...),
			signer:         validCA.key,
			wantIssuerName: "test-ca",
			wantValidity:   options.DefaultServingCertValidity,
		},
		"custom validity": {
			caPEM:               validCA.certPEM,
			signer:              validCA.key,
			servingCertValidity: 24 * time.Hour,
			wantIssuerName:      "test-ca",
			wantValidity:        24 * time.Hour,
		},
		"validity shorter than the minimum": {
			caPEM:               validCA.certPEM,
			signer:              validCA.key,
			servingCertValidity: time.Minute,
			wantErr:             "shorter than the minimum",
		},
		"no CA certificate matches the key": {
			caPEM:   otherCA.certPEM,
			signer:  validCA.key,
			wantErr: "none of the webhook CA certificates matches the public key",
		},
		"the matching certificate is not a CA": {
			caPEM:   notCA.certPEM,
			signer:  notCA.key,
			wantErr: "is not a CA certificate",
		},
		"the matching CA certificate cannot sign certificates": {
			caPEM:   noCertSignCA.certPEM,
			signer:  noCertSignCA.key,
			wantErr: "is not allowed to sign certificates",
		},
		"the signer returns no public key (e.g., a failing KMS plugin)": {
			caPEM:   validCA.certPEM,
			signer:  nilPublicKeySigner{Signer: validCA.key},
			wantErr: "failed to get the public key",
		},
		"non-certificate PEM blocks in the CA file are skipped": {
			caPEM: append(pem.EncodeToMemory(&pem.Block{Type: "PUBLIC KEY", Bytes: []byte("ignored")}),
				validCA.certPEM...),
			signer:         validCA.key,
			wantIssuerName: "test-ca",
			wantValidity:   options.DefaultServingCertValidity,
		},
		"malformed certificate in the CA file": {
			caPEM:   pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: []byte("not DER")}),
			signer:  validCA.key,
			wantErr: "failed to parse a webhook CA certificate",
		},
		"no PEM encoded certificate": {
			caPEM:   []byte("not a certificate"),
			signer:  validCA.key,
			wantErr: "no PEM encoded certificate found",
		},
	}
	for name, tc := range testCases {
		t.Run(name, func(t *testing.T) {
			got, err := NewExternalCA(tc.caPEM, tc.signer, tc.servingCertValidity)
			if tc.wantErr != "" {
				if err == nil || !strings.Contains(err.Error(), tc.wantErr) {
					t.Fatalf("NewExternalCA() error = %v, want error containing %q", err, tc.wantErr)
				}
				return
			}
			if err != nil {
				t.Fatalf("NewExternalCA() = %v, want no error", err)
			}
			if got.issuer.Subject.CommonName != tc.wantIssuerName {
				t.Errorf("NewExternalCA() issuer = %q, want %q", got.issuer.Subject.CommonName, tc.wantIssuerName)
			}
			if got.servingCertValidity != tc.wantValidity {
				t.Errorf("NewExternalCA() servingCertValidity = %s, want %s", got.servingCertValidity, tc.wantValidity)
			}
			if !bytes.Equal(got.caPEM, tc.caPEM) {
				t.Errorf("NewExternalCA() caPEM = %q, want %q", got.caPEM, tc.caPEM)
			}
		})
	}
}

// verifyServingCert checks that certPEM/keyPEM form a key pair, that the certificate chains to
// caPEM, and returns the parsed serving certificate.
func verifyServingCert(t *testing.T, certPEM, keyPEM, caPEM []byte, dnsName string, at time.Time) *x509.Certificate {
	t.Helper()
	pair, err := tls.X509KeyPair(certPEM, keyPEM)
	if err != nil {
		t.Fatalf("tls.X509KeyPair() = %v, want no error", err)
	}
	if len(pair.Certificate) != 2 {
		t.Fatalf("serving certificate chain length = %d, want 2 (serving certificate and CA)", len(pair.Certificate))
	}
	leaf, err := x509.ParseCertificate(pair.Certificate[0])
	if err != nil {
		t.Fatalf("x509.ParseCertificate() = %v, want no error", err)
	}
	roots := x509.NewCertPool()
	if !roots.AppendCertsFromPEM(caPEM) {
		t.Fatalf("AppendCertsFromPEM() = false, want true")
	}
	if _, err := leaf.Verify(x509.VerifyOptions{
		DNSName:     dnsName,
		Roots:       roots,
		CurrentTime: at,
		KeyUsages:   []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
	}); err != nil {
		t.Fatalf("serving certificate Verify() = %v, want no error", err)
	}
	return leaf
}

func TestIssueServingCert(t *testing.T) {
	dnsNames := []string{"fleetwebhook.fleet-system.svc", "fleetwebhook.fleet-system.svc.cluster.local"}

	rsaKey, err := rsa.GenerateKey(rand.Reader, 2048)
	if err != nil {
		t.Fatalf("rsa.GenerateKey() = %v, want no error", err)
	}

	testCases := map[string]struct {
		caKey               crypto.Signer
		caNotAfter          time.Time
		servingCertValidity time.Duration
		wantNotBefore       time.Time
		wantNotAfter        time.Time
		wantErr             string
	}{
		"1-day serving certificate": {
			caNotAfter:          testNow.AddDate(1, 0, 0),
			servingCertValidity: 24 * time.Hour,
			wantNotBefore:       testNow.Add(-externalCAServingCertBackdate),
			wantNotAfter:        testNow.Add(24 * time.Hour),
		},
		"RSA CA key (e.g., an RSA-HSM key in Key Vault)": {
			caKey:         rsaKey,
			caNotAfter:    testNow.AddDate(1, 0, 0),
			wantNotBefore: testNow.Add(-externalCAServingCertBackdate),
			wantNotAfter:  testNow.Add(options.DefaultServingCertValidity),
		},
		"long-lived CA": {
			caNotAfter:    testNow.AddDate(1, 0, 0),
			wantNotBefore: testNow.Add(-externalCAServingCertBackdate),
			wantNotAfter:  testNow.Add(options.DefaultServingCertValidity),
		},
		"CA expiring before a full serving certificate lifetime": {
			caNotAfter:    testNow.Add(24 * time.Hour),
			wantNotBefore: testNow.Add(-externalCAServingCertBackdate),
			wantNotAfter:  testNow.Add(24 * time.Hour),
		},
		"expired CA": {
			caNotAfter: testNow,
			wantErr:    "expired",
		},
	}
	for name, tc := range testCases {
		t.Run(name, func(t *testing.T) {
			testCA := newTestCA(t, "test-ca", true, x509.KeyUsageCertSign, tc.caNotAfter)
			if tc.caKey != nil {
				testCA = newTestCAWithKey(t, tc.caKey, "test-ca", true, x509.KeyUsageCertSign, tc.caNotAfter)
			}
			ca, err := NewExternalCA(testCA.certPEM, testCA.key, tc.servingCertValidity)
			if err != nil {
				t.Fatalf("NewExternalCA() = %v, want no error", err)
			}

			certPEM, keyPEM, notBefore, notAfter, err := ca.issueServingCert("fleetwebhook.cert.server", dnsNames, testNow)
			if tc.wantErr != "" {
				if err == nil || !strings.Contains(err.Error(), tc.wantErr) {
					t.Fatalf("issueServingCert() error = %v, want error containing %q", err, tc.wantErr)
				}
				return
			}
			if err != nil {
				t.Fatalf("issueServingCert() = %v, want no error", err)
			}
			if !notBefore.Equal(tc.wantNotBefore) || !notAfter.Equal(tc.wantNotAfter) {
				t.Errorf("issueServingCert() validity = [%s, %s], want [%s, %s]", notBefore, notAfter, tc.wantNotBefore, tc.wantNotAfter)
			}

			leaf := verifyServingCert(t, certPEM, keyPEM, testCA.certPEM, dnsNames[0], testNow)
			if diff := cmp.Diff(dnsNames, leaf.DNSNames); diff != "" {
				t.Errorf("serving certificate DNS names mismatch (-want +got):\n%s", diff)
			}
			if leaf.IsCA {
				t.Errorf("serving certificate IsCA = true, want false")
			}
		})
	}
}

func TestLoadExternalCA(t *testing.T) {
	testCA := newValidTestCA(t)
	caCertFile := filepath.Join(t.TempDir(), "ca.crt")
	if err := os.WriteFile(caCertFile, testCA.certPEM, 0600); err != nil {
		t.Fatalf("os.WriteFile() = %v, want no error", err)
	}
	// The sigstore fake KMS provider signs with the private key found in the context.
	ctx := context.WithValue(context.Background(), fake.KmsCtxKey{}, crypto.PrivateKey(testCA.key))

	testCases := map[string]struct {
		caCertFile string
		keyRef     string
		wantErr    string
	}{
		"key served by a sigstore KMS provider": {
			caCertFile: caCertFile,
			keyRef:     fake.ReferenceScheme + "webhook-ca",
		},
		"missing CA certificate file": {
			caCertFile: filepath.Join(t.TempDir(), "missing.crt"),
			keyRef:     fake.ReferenceScheme + "webhook-ca",
			wantErr:    "failed to read the webhook CA certificate file",
		},
		"no provider or plugin for the key reference": {
			caCertFile: caCertFile,
			keyRef:     "nosuchkms://webhook-ca",
			wantErr:    "failed to load the webhook CA signing key",
		},
	}
	for name, tc := range testCases {
		t.Run(name, func(t *testing.T) {
			ca, err := LoadExternalCA(ctx, tc.caCertFile, tc.keyRef, 0)
			if tc.wantErr != "" {
				if err == nil || !strings.Contains(err.Error(), tc.wantErr) {
					t.Fatalf("LoadExternalCA() error = %v, want error containing %q", err, tc.wantErr)
				}
				return
			}
			if err != nil {
				t.Fatalf("LoadExternalCA() = %v, want no error", err)
			}

			// Signing goes through the sigstore signer, not the in-memory key.
			certPEM, keyPEM, _, _, err := ca.issueServingCert("fleetwebhook.cert.server", []string{"fleetwebhook.fleet-system.svc"}, testNow)
			if err != nil {
				t.Fatalf("issueServingCert() = %v, want no error", err)
			}
			verifyServingCert(t, certPEM, keyPEM, testCA.certPEM, "fleetwebhook.fleet-system.svc", testNow)
		})
	}
}

// nilPublicKeySigner is a crypto.Signer that cannot report its public key, like a sigstore KMS
// plugin signer whose PublicKey call failed.
type nilPublicKeySigner struct {
	crypto.Signer
}

func (nilPublicKeySigner) Public() crypto.PublicKey {
	return nil
}

// togglingSigner is a crypto.Signer whose signing can be made to fail.
type togglingSigner struct {
	crypto.Signer
	fail atomic.Bool
}

func (s *togglingSigner) Sign(r io.Reader, digest []byte, opts crypto.SignerOpts) ([]byte, error) {
	if s.fail.Load() {
		return nil, errors.New("KMS unavailable")
	}
	return s.Signer.Sign(r, digest, opts)
}

func newTestRotator(t *testing.T, signer crypto.Signer, testCA testCA, fakeClock *clocktesting.FakeClock) *servingCertRotator {
	t.Helper()
	ca, err := NewExternalCA(testCA.certPEM, signer, 0)
	if err != nil {
		t.Fatalf("NewExternalCA() = %v, want no error", err)
	}
	return &servingCertRotator{
		ca:         ca,
		certDir:    filepath.Join(t.TempDir(), "serving-certs"),
		commonName: "fleetwebhook.cert.server",
		dnsNames:   []string{"fleetwebhook.fleet-system.svc"},
		clock:      fakeClock,
	}
}

// readServingCertNotAfter returns the NotAfter of the serving certificate written to certDir.
func readServingCertNotAfter(t *testing.T, certDir string) time.Time {
	t.Helper()
	pair, err := tls.LoadX509KeyPair(filepath.Join(certDir, fleetWebhookCertFileName), filepath.Join(certDir, fleetWebhookKeyFileName))
	if err != nil {
		t.Fatalf("tls.LoadX509KeyPair() = %v, want no error", err)
	}
	leaf, err := x509.ParseCertificate(pair.Certificate[0])
	if err != nil {
		t.Fatalf("x509.ParseCertificate() = %v, want no error", err)
	}
	return leaf.NotAfter
}

func TestServingCertRotatorRotate(t *testing.T) {
	testCA := newValidTestCA(t)
	fakeClock := clocktesting.NewFakeClock(testNow)
	r := newTestRotator(t, testCA.key, testCA, fakeClock)

	if err := r.rotate(); err != nil {
		t.Fatalf("rotate() = %v, want no error", err)
	}
	if got, want := readServingCertNotAfter(t, r.certDir), testNow.Add(options.DefaultServingCertValidity); !got.Equal(want) {
		t.Errorf("written serving certificate NotAfter = %s, want %s", got, want)
	}
	lifetime := options.DefaultServingCertValidity + externalCAServingCertBackdate
	if got, want := r.renewAt(), testNow.Add(-externalCAServingCertBackdate).Add(lifetime*2/3); !got.Equal(want) {
		t.Errorf("renewAt() = %s, want %s", got, want)
	}

	if got, want := testutil.ToFloat64(hubmetrics.FleetWebhookServingCertExpirationTimestampSeconds), float64(testNow.Add(options.DefaultServingCertValidity).Unix()); got != want {
		t.Errorf("serving certificate expiration metric = %v, want %v", got, want)
	}
	if got, want := testutil.ToFloat64(hubmetrics.FleetWebhookCACertExpirationTimestampSeconds), float64(testCA.cert.NotAfter.Unix()); got != want {
		t.Errorf("CA certificate expiration metric = %v, want %v", got, want)
	}

	// Only the certificate and key are left behind (no temporary files), readable by the owner only.
	entries, err := os.ReadDir(r.certDir)
	if err != nil {
		t.Fatalf("os.ReadDir() = %v, want no error", err)
	}
	var gotFiles []string
	for _, e := range entries {
		gotFiles = append(gotFiles, e.Name())
		info, err := e.Info()
		if err != nil {
			t.Fatalf("Info() = %v, want no error", err)
		}
		if got := info.Mode().Perm(); got != 0600 {
			t.Errorf("%s mode = %o, want 600", e.Name(), got)
		}
	}
	if diff := cmp.Diff([]string{fleetWebhookCertFileName, fleetWebhookKeyFileName}, gotFiles); diff != "" {
		t.Errorf("certificate directory contents mismatch (-want +got):\n%s", diff)
	}

	// A second rotation replaces the files in place.
	fakeClock.Step(time.Hour)
	if err := r.rotate(); err != nil {
		t.Fatalf("rotate() = %v, want no error", err)
	}
	if got, want := readServingCertNotAfter(t, r.certDir), testNow.Add(time.Hour).Add(options.DefaultServingCertValidity); !got.Equal(want) {
		t.Errorf("rewritten serving certificate NotAfter = %s, want %s", got, want)
	}
}

// waitForTimer waits until the rotator is blocked on the fake clock.
func waitForTimer(t *testing.T, fakeClock *clocktesting.FakeClock) {
	t.Helper()
	deadline := time.Now().Add(10 * time.Second)
	for !fakeClock.HasWaiters() {
		if time.Now().After(deadline) {
			t.Fatalf("the rotator did not wait on the clock in time")
		}
		time.Sleep(time.Millisecond)
	}
}

func TestServingCertRotatorStart(t *testing.T) {
	testCA := newValidTestCA(t)
	fakeClock := clocktesting.NewFakeClock(testNow)
	signer := &togglingSigner{Signer: testCA.key}
	r := newTestRotator(t, signer, testCA, fakeClock)
	if err := r.rotate(); err != nil {
		t.Fatalf("rotate() = %v, want no error", err)
	}
	firstRenewAt := r.renewAt()

	ctx, cancel := context.WithCancel(context.Background())
	done := make(chan error)
	go func() { done <- r.Start(ctx) }()

	// Renewal fails at first: the rotator keeps the current certificate and retries with backoff.
	signer.fail.Store(true)
	waitForTimer(t, fakeClock)
	fakeClock.SetTime(firstRenewAt)
	waitForTimer(t, fakeClock)
	if got, want := readServingCertNotAfter(t, r.certDir), testNow.Add(options.DefaultServingCertValidity); !got.Equal(want) {
		t.Fatalf("serving certificate NotAfter after a failed renewal = %s, want %s (unchanged)", got, want)
	}

	// Once signing works again, the retry renews the certificate.
	signer.fail.Store(false)
	retryAt := firstRenewAt.Add(externalCARenewRetryMinDelay)
	fakeClock.SetTime(retryAt)
	waitForTimer(t, fakeClock)
	if got, want := readServingCertNotAfter(t, r.certDir), retryAt.Add(options.DefaultServingCertValidity); !got.Equal(want) {
		t.Errorf("serving certificate NotAfter after the retry = %s, want %s", got, want)
	}

	cancel()
	select {
	case err := <-done:
		if err != nil {
			t.Errorf("Start() = %v, want no error", err)
		}
	case <-time.After(10 * time.Second):
		t.Fatalf("Start() did not return after the context was cancelled")
	}
}

func TestServingCertRotatorRotateFailureKeepsCurrentCert(t *testing.T) {
	testCA := newValidTestCA(t)
	fakeClock := clocktesting.NewFakeClock(testNow)
	r := newTestRotator(t, testCA.key, testCA, fakeClock)
	if err := r.rotate(); err != nil {
		t.Fatalf("rotate() = %v, want no error", err)
	}
	wantNotBefore, wantNotAfter := r.notBefore, r.notAfter

	// The certificate directory can no longer be written to: a file now takes its place.
	r.certDir = filepath.Join(t.TempDir(), "not-a-directory")
	if err := os.WriteFile(r.certDir, nil, 0600); err != nil {
		t.Fatalf("os.WriteFile() = %v, want no error", err)
	}
	fakeClock.Step(time.Hour)
	if err := r.rotate(); err == nil {
		t.Fatalf("rotate() = nil, want an error")
	}
	if !r.notBefore.Equal(wantNotBefore) || !r.notAfter.Equal(wantNotAfter) {
		t.Errorf("rotator validity after a failed rotation = [%s, %s], want [%s, %s] (unchanged)", r.notBefore, r.notAfter, wantNotBefore, wantNotAfter)
	}
}

func TestServingCertRotatorRunsOnEveryReplica(t *testing.T) {
	r := &servingCertRotator{}
	if r.NeedLeaderElection() {
		t.Errorf("NeedLeaderElection() = true, want false (every replica renews its own certificate)")
	}
}

func TestNextRenewRetryDelay(t *testing.T) {
	testCases := map[string]struct {
		last time.Duration
		want time.Duration
	}{
		"first retry":         {last: 0, want: externalCARenewRetryMinDelay},
		"doubles":             {last: 2 * time.Minute, want: 4 * time.Minute},
		"capped at max delay": {last: 8 * time.Minute, want: externalCARenewRetryMaxDelay},
	}
	for name, tc := range testCases {
		t.Run(name, func(t *testing.T) {
			if got := nextRenewRetryDelay(tc.last); got != tc.want {
				t.Errorf("nextRenewRetryDelay(%s) = %s, want %s", tc.last, got, tc.want)
			}
		})
	}
}

func TestNewWebhookConfigWithExternalCA(t *testing.T) {
	t.Setenv("POD_NAMESPACE", "fleet-system")
	// NewWebhookConfig issues the certificate at the current (real) time.
	testCA := newTestCA(t, "test-ca", true, x509.KeyUsageCertSign, time.Now().AddDate(1, 0, 0))
	ca, err := NewExternalCA(testCA.certPEM, testCA.key, 0)
	if err != nil {
		t.Fatalf("NewExternalCA() = %v, want no error", err)
	}

	t.Run("issues the serving certificate and trusts the external CA", func(t *testing.T) {
		certDir := filepath.Join(t.TempDir(), "serving-certs")
		w, err := NewWebhookConfig(nil, "fleetwebhook", 443, nil, certDir, false, false, false, false, false, "fleet-webhook-certificate", nil, false, ca)
		if err != nil {
			t.Fatalf("NewWebhookConfig() = %v, want no error", err)
		}
		if !bytes.Equal(w.caPEM, testCA.certPEM) {
			t.Errorf("NewWebhookConfig() caPEM = %q, want the external CA certificate %q", w.caPEM, testCA.certPEM)
		}
		if w.ServingCertRotator() == nil {
			t.Errorf("ServingCertRotator() = nil, want a rotator")
		}
		certPEM, err := os.ReadFile(filepath.Join(certDir, fleetWebhookCertFileName))
		if err != nil {
			t.Fatalf("os.ReadFile() = %v, want no error", err)
		}
		keyPEM, err := os.ReadFile(filepath.Join(certDir, fleetWebhookKeyFileName))
		if err != nil {
			t.Fatalf("os.ReadFile() = %v, want no error", err)
		}
		verifyServingCert(t, certPEM, keyPEM, testCA.certPEM, "fleetwebhook.fleet-system.svc", time.Now())
	})

	t.Run("fails and counts the failure when the serving certificate cannot be issued", func(t *testing.T) {
		expiredCA := newTestCA(t, "expired-ca", true, x509.KeyUsageCertSign, time.Now().Add(-time.Minute))
		ca, err := NewExternalCA(expiredCA.certPEM, expiredCA.key, 0)
		if err != nil {
			t.Fatalf("NewExternalCA() = %v, want no error", err)
		}
		before := testutil.ToFloat64(hubmetrics.FleetWebhookServingCertIssuanceFailuresTotal)
		if _, err := NewWebhookConfig(nil, "fleetwebhook", 443, nil, t.TempDir(), false, false, false, false, false, "fleet-webhook-certificate", nil, false, ca); err == nil {
			t.Fatalf("NewWebhookConfig() = nil error, want an error")
		}
		if got := testutil.ToFloat64(hubmetrics.FleetWebhookServingCertIssuanceFailuresTotal) - before; got != 1 {
			t.Errorf("issuance failure metric increase = %v, want 1", got)
		}
	})

	t.Run("cannot be combined with cert-manager", func(t *testing.T) {
		_, err := NewWebhookConfig(nil, "fleetwebhook", 443, nil, t.TempDir(), false, false, true, false, true, "fleet-webhook-certificate", nil, false, ca)
		if err == nil {
			t.Fatalf("NewWebhookConfig() = nil error, want an error")
		}
	})

	t.Run("no rotator without an external CA", func(t *testing.T) {
		w, err := NewWebhookConfig(nil, "fleetwebhook", 443, nil, t.TempDir(), false, false, false, false, false, "fleet-webhook-certificate", nil, false, nil)
		if err != nil {
			t.Fatalf("NewWebhookConfig() = %v, want no error", err)
		}
		if w.ServingCertRotator() != nil {
			t.Errorf("ServingCertRotator() = %v, want nil", w.ServingCertRotator())
		}
	})
}

func TestNewWebhookConfigFromOptionsWithExternalCA(t *testing.T) {
	t.Setenv("POD_NAMESPACE", "fleet-system")
	testCA := newValidTestCA(t)
	caCertFile := filepath.Join(t.TempDir(), "ca.crt")
	if err := os.WriteFile(caCertFile, testCA.certPEM, 0600); err != nil {
		t.Fatalf("os.WriteFile() = %v, want no error", err)
	}

	testCases := map[string]struct {
		caCertFile string
		wantErr    string
	}{
		"the flags reach the KMS: the fake KMS key does not match the CA certificate": {
			caCertFile: caCertFile,
			wantErr:    "none of the webhook CA certificates matches the public key",
		},
		"missing CA certificate file": {
			caCertFile: filepath.Join(t.TempDir(), "missing.crt"),
			wantErr:    "failed to read the webhook CA certificate file",
		},
	}
	for name, tc := range testCases {
		t.Run(name, func(t *testing.T) {
			opts := &options.Options{
				WebhookAndAdmissionPolicyOpts: options.WebhookAndAdmissionPolicyOptions{
					ServiceName:          "fleetwebhook",
					ClientConnectionType: "service",
					CACertFile:           tc.caCertFile,
					// Without a key in the context, the sigstore fake KMS signs with a key of its own.
					CAKeyRef:            fake.ReferenceScheme + "webhook-ca",
					ServingCertValidity: 24 * time.Hour,
				},
			}
			_, err := NewWebhookConfigFromOptions(nil, opts, 443)
			if err == nil || !strings.Contains(err.Error(), tc.wantErr) {
				t.Fatalf("NewWebhookConfigFromOptions() error = %v, want error containing %q", err, tc.wantErr)
			}
		})
	}
}
