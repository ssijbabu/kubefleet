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
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"errors"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"time"

	"github.com/sigstore/sigstore/pkg/signature/kms"
	"k8s.io/klog/v2"
	"k8s.io/utils/clock"

	hubmetrics "github.com/kubefleet-dev/kubefleet/pkg/metrics/hub"
)

const (
	// externalCALoadTimeout bounds how long loading the external CA signing key may take at startup.
	externalCALoadTimeout = time.Minute

	// externalCAServingCertValidity is the lifetime of a webhook serving certificate issued by
	// the external CA. The certificate is renewed after two thirds of its lifetime has passed.
	externalCAServingCertValidity = 30 * 24 * time.Hour
	// externalCAServingCertBackdate is how far in the past the NotBefore field of a serving
	// certificate is set, to tolerate clock skew between the hub agent and the API server.
	externalCAServingCertBackdate = 5 * time.Minute

	// externalCARenewRetryMinDelay and externalCARenewRetryMaxDelay bound the backoff between
	// failed attempts to renew the serving certificate.
	externalCARenewRetryMinDelay = time.Minute
	externalCARenewRetryMaxDelay = 10 * time.Minute
)

// ExternalCA issues webhook serving certificates signed by a CA whose private key is held
// outside of the hub agent, e.g., in a KMS or an HSM. Only the CA signing operation is delegated
// to the key holder; the private key of each serving certificate is generated in memory.
type ExternalCA struct {
	// caPEM is the content of the CA certificate file, used as-is for the webhook CA bundle.
	// It may hold more than one CA certificate, e.g., the old and the new one during a CA rotation.
	caPEM []byte
	// issuer is the CA certificate in caPEM whose public key matches the signer.
	issuer *x509.Certificate
	// signer signs with the private key of the CA.
	signer crypto.Signer
}

// LoadExternalCA loads the CA certificate(s) from caCertFile and resolves keyRef, a key reference
// URI such as azurekms://<vault>.vault.azure.net/<key>, into a signer with the sigstore KMS library.
//
// KubeFleet registers no vendor-specific KMS provider; a key reference is served by a plugin program
// named sigstore-kms-<scheme> on the PATH of the hub agent, which keeps the hub agent vendor-neutral.
func LoadExternalCA(ctx context.Context, caCertFile, keyRef string) (*ExternalCA, error) {
	caPEM, err := os.ReadFile(filepath.Clean(caCertFile))
	if err != nil {
		return nil, fmt.Errorf("failed to read the webhook CA certificate file %q: %w", caCertFile, err)
	}

	sv, err := kms.Get(ctx, keyRef, crypto.SHA256)
	if err != nil {
		return nil, fmt.Errorf("failed to load the webhook CA signing key %q: %w", keyRef, err)
	}
	// The signer is used for as long as the hub agent runs, so it must not inherit the (bounded)
	// context used for loading.
	signer, _, err := sv.CryptoSigner(context.Background(), func(err error) {
		klog.ErrorS(err, "The webhook CA signing key operation failed", "keyRef", keyRef)
	})
	if err != nil {
		return nil, fmt.Errorf("failed to get a signer for the webhook CA signing key %q: %w", keyRef, err)
	}
	return NewExternalCA(caPEM, signer)
}

// NewExternalCA returns an ExternalCA that signs with signer. caPEM must contain the CA
// certificate matching the signer's public key; it may contain other CA certificates as well.
func NewExternalCA(caPEM []byte, signer crypto.Signer) (*ExternalCA, error) {
	caCerts, err := parseCertificates(caPEM)
	if err != nil {
		return nil, err
	}

	pub := signer.Public()
	if pub == nil {
		return nil, errors.New("failed to get the public key of the webhook CA signing key")
	}
	var issuer *x509.Certificate
	for _, cert := range caCerts {
		if k, ok := cert.PublicKey.(interface{ Equal(crypto.PublicKey) bool }); ok && k.Equal(pub) {
			issuer = cert
			break
		}
	}
	if issuer == nil {
		return nil, errors.New("none of the webhook CA certificates matches the public key of the webhook CA signing key")
	}
	if !issuer.BasicConstraintsValid || !issuer.IsCA {
		return nil, fmt.Errorf("the webhook CA certificate %q is not a CA certificate", issuer.Subject.String())
	}
	if issuer.KeyUsage != 0 && issuer.KeyUsage&x509.KeyUsageCertSign == 0 {
		return nil, fmt.Errorf("the webhook CA certificate %q is not allowed to sign certificates", issuer.Subject.String())
	}

	return &ExternalCA{
		caPEM:  caPEM,
		issuer: issuer,
		signer: &cachedPublicKeySigner{Signer: signer, public: issuer.PublicKey},
	}, nil
}

// issueServingCert issues a serving certificate for the given DNS names, valid from now. The
// returned certificate PEM holds the serving certificate followed by the issuing CA certificate.
func (ca *ExternalCA) issueServingCert(commonName string, dnsNames []string, now time.Time) (certPEM, keyPEM []byte, notBefore, notAfter time.Time, err error) {
	if !now.Before(ca.issuer.NotAfter) {
		return nil, nil, time.Time{}, time.Time{}, fmt.Errorf("the webhook CA certificate %q expired at %s", ca.issuer.Subject.String(), ca.issuer.NotAfter)
	}

	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return nil, nil, time.Time{}, time.Time{}, fmt.Errorf("failed to generate the serving certificate key: %w", err)
	}
	serial, err := rand.Int(rand.Reader, new(big.Int).Lsh(big.NewInt(1), 128))
	if err != nil {
		return nil, nil, time.Time{}, time.Time{}, fmt.Errorf("failed to generate the serving certificate serial number: %w", err)
	}

	notBefore = now.Add(-externalCAServingCertBackdate)
	notAfter = now.Add(externalCAServingCertValidity)
	// A serving certificate must not outlive the CA that issues it.
	if notAfter.After(ca.issuer.NotAfter) {
		notAfter = ca.issuer.NotAfter
	}
	template := &x509.Certificate{
		SerialNumber:          serial,
		Subject:               pkix.Name{CommonName: commonName},
		DNSNames:              dnsNames,
		NotBefore:             notBefore,
		NotAfter:              notAfter,
		KeyUsage:              x509.KeyUsageDigitalSignature,
		ExtKeyUsage:           []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
		BasicConstraintsValid: true,
	}
	certDER, err := x509.CreateCertificate(rand.Reader, template, ca.issuer, &key.PublicKey, ca.signer)
	if err != nil {
		return nil, nil, time.Time{}, time.Time{}, fmt.Errorf("failed to sign the serving certificate with the webhook CA: %w", err)
	}

	certBuf := new(bytes.Buffer)
	for _, der := range [][]byte{certDER, ca.issuer.Raw} {
		if err := pem.Encode(certBuf, &pem.Block{Type: "CERTIFICATE", Bytes: der}); err != nil {
			return nil, nil, time.Time{}, time.Time{}, err
		}
	}
	keyDER, err := x509.MarshalECPrivateKey(key)
	if err != nil {
		return nil, nil, time.Time{}, time.Time{}, fmt.Errorf("failed to encode the serving certificate key: %w", err)
	}
	keyPEM = pem.EncodeToMemory(&pem.Block{Type: "EC PRIVATE KEY", Bytes: keyDER})
	return certBuf.Bytes(), keyPEM, notBefore, notAfter, nil
}

// parseCertificates parses all the PEM encoded certificates in data.
func parseCertificates(data []byte) ([]*x509.Certificate, error) {
	var certs []*x509.Certificate
	for block, rest := pem.Decode(data); block != nil; block, rest = pem.Decode(rest) {
		if block.Type != "CERTIFICATE" {
			continue
		}
		cert, err := x509.ParseCertificate(block.Bytes)
		if err != nil {
			return nil, fmt.Errorf("failed to parse a webhook CA certificate: %w", err)
		}
		certs = append(certs, cert)
	}
	if len(certs) == 0 {
		return nil, errors.New("no PEM encoded certificate found in the webhook CA certificate data")
	}
	return certs, nil
}

// cachedPublicKeySigner is a crypto.Signer that answers Public() from the CA certificate instead
// of asking the key holder (e.g., invoking a KMS plugin program) on every call.
type cachedPublicKeySigner struct {
	crypto.Signer
	public crypto.PublicKey
}

// Public returns the cached public key.
func (s *cachedPublicKeySigner) Public() crypto.PublicKey {
	return s.public
}

// servingCertRotator issues the webhook serving certificate with an external CA and re-issues it
// before it expires. It runs on every hub agent replica, not just the leader, as each replica
// serves its own certificate; the webhook server picks up the rewritten files by itself.
type servingCertRotator struct {
	ca         *ExternalCA
	certDir    string
	commonName string
	dnsNames   []string
	clock      clock.Clock

	// notBefore and notAfter are the validity period of the serving certificate in use.
	notBefore time.Time
	notAfter  time.Time
}

// rotate issues a new serving certificate and writes it, with its key, to the certificate directory.
func (r *servingCertRotator) rotate() error {
	certPEM, keyPEM, notBefore, notAfter, err := r.ca.issueServingCert(r.commonName, r.dnsNames, r.clock.Now())
	if err != nil {
		return err
	}
	if err := writeServingCertFiles(certPEM, keyPEM, r.certDir); err != nil {
		return err
	}
	r.notBefore, r.notAfter = notBefore, notAfter
	hubmetrics.FleetWebhookServingCertExpirationTimestampSeconds.Set(float64(notAfter.Unix()))
	hubmetrics.FleetWebhookCACertExpirationTimestampSeconds.Set(float64(r.ca.issuer.NotAfter.Unix()))
	klog.V(2).InfoS("Issued the webhook serving certificate with the external CA", "notAfter", notAfter, "caNotAfter", r.ca.issuer.NotAfter)
	return nil
}

// renewAt returns the time when the serving certificate in use should be renewed, which is after
// two thirds of its lifetime.
func (r *servingCertRotator) renewAt() time.Time {
	return r.notBefore.Add(r.notAfter.Sub(r.notBefore) * 2 / 3)
}

// Start renews the serving certificate until ctx is done. It implements manager.Runnable.
func (r *servingCertRotator) Start(ctx context.Context) error {
	var retryDelay time.Duration
	for {
		wait := retryDelay
		if wait == 0 {
			wait = r.renewAt().Sub(r.clock.Now())
		}
		timer := r.clock.NewTimer(wait)
		select {
		case <-ctx.Done():
			timer.Stop()
			return nil
		case <-timer.C():
		}

		if err := r.rotate(); err != nil {
			hubmetrics.FleetWebhookServingCertIssuanceFailuresTotal.Inc()
			retryDelay = nextRenewRetryDelay(retryDelay)
			klog.ErrorS(err, "Failed to renew the webhook serving certificate; will retry", "retryAfter", retryDelay, "notAfter", r.notAfter)
			continue
		}
		retryDelay = 0
	}
}

// NeedLeaderElection returns false, as every hub agent replica must renew its own certificate.
// It implements manager.LeaderElectionRunnable.
func (r *servingCertRotator) NeedLeaderElection() bool {
	return false
}

// nextRenewRetryDelay returns the delay before the next renewal attempt after a failed one.
func nextRenewRetryDelay(last time.Duration) time.Duration {
	if last == 0 {
		return externalCARenewRetryMinDelay
	}
	return min(last*2, externalCARenewRetryMaxDelay)
}

// writeServingCertFiles writes the serving certificate and key files to certDir. Each file is
// replaced atomically, so that the webhook server never reads a partially written file.
func writeServingCertFiles(certPEM, keyPEM []byte, certDir string) error {
	if err := os.MkdirAll(certDir, 0755); err != nil {
		return fmt.Errorf("could not create directory %q to store certificates: %w", certDir, err)
	}
	// Write the key first: if the certificate write then fails, the webhook server fails to load
	// the mismatched pair and keeps serving the previous certificate.
	if err := writeFileAtomically(filepath.Join(certDir, fleetWebhookKeyFileName), keyPEM); err != nil {
		return err
	}
	return writeFileAtomically(filepath.Join(certDir, fleetWebhookCertFileName), certPEM)
}

// writeFileAtomically writes data to a temporary file (readable by the owner only) in the same
// directory, then renames it to path.
func writeFileAtomically(path string, data []byte) error {
	f, err := os.CreateTemp(filepath.Dir(path), "."+filepath.Base(path)+".tmp-*")
	if err != nil {
		return fmt.Errorf("could not create a temporary file for %q: %w", path, err)
	}
	tmpPath := f.Name()
	defer os.Remove(tmpPath) // No-op once renamed.

	if _, err := f.Write(data); err != nil {
		f.Close()
		return fmt.Errorf("could not write %q: %w", tmpPath, err)
	}
	if err := f.Close(); err != nil {
		return fmt.Errorf("could not close %q: %w", tmpPath, err)
	}
	if err := os.Rename(tmpPath, path); err != nil {
		return fmt.Errorf("could not replace %q: %w", path, err)
	}
	return nil
}
