//! The ACVP tests of ML-DSA (FIPS 204), for each parameter set: every
//! vector of key generation (the public key of each seed; the API keeps the
//! private key to itself) and of signature verification (pure ML-DSA, with
//! the message and its context string, and the internal interface, with
//! `M′` or `μ`). The signature generation vectors give expanded private keys
//! without their seeds, which the API does not accept, so signing is checked
//! by verifying its signatures, and against Wycheproof's seed vectors
//! (`tests/wycheproof/mldsa*.rs`).

/// Defines the tests of the parameter set named `$name` (`"ML-DSA-44"`), of
/// the module `$module` and its key types.
// Used by the parameter sets' files, on the architectures they support.
#[allow(unused_macros)]
macro_rules! mldsa_tests {
    ($name:literal, $module:ident, $SigningKey:ident, $VerifyingKey:ident) => {
        use serde::Deserialize;
        use verified_garbage::hashes::sha3::Shake256;
        use verified_garbage::$module::{Error, $SigningKey, $VerifyingKey};

        #[derive(Deserialize)]
        struct File<T> {
            #[serde(rename = "testGroups")]
            groups: Vec<Group<T>>,
        }

        #[derive(Deserialize)]
        struct Group<T> {
            #[serde(rename = "parameterSet")]
            parameter_set: String,
            #[serde(rename = "signatureInterface", default)]
            interface: String,
            #[serde(rename = "preHash", default)]
            pre_hash: String,
            #[serde(rename = "externalMu", default)]
            external_mu: bool,
            tests: Vec<T>,
        }

        #[derive(Deserialize)]
        struct KeyGen {
            seed: String,
            pk: String,
        }

        #[derive(Deserialize)]
        struct SigVer {
            pk: String,
            #[serde(default)]
            message: String,
            #[serde(default)]
            context: String,
            #[serde(default)]
            mu: String,
            signature: String,
            #[serde(rename = "testPassed")]
            passed: bool,
        }

        fn unhex(s: &str) -> Vec<u8> {
            assert_eq!(s.len() % 2, 0);
            (0..s.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
                .collect()
        }

        /// The groups of the parameter set in the vendored file `json`.
        fn groups<T: serde::de::DeserializeOwned>(json: &str) -> Vec<Group<T>> {
            let file: File<T> = serde_json::from_str(json).unwrap();
            let groups: Vec<Group<T>> = file
                .groups
                .into_iter()
                .filter(|g| g.parameter_set == $name)
                .collect();
            assert!(!groups.is_empty());
            groups
        }

        #[test]
        fn keygen() {
            let json = include_str!(
                "../../vectors/nist-acvp/ML-DSA-keyGen-FIPS204/internalProjection.json"
            );
            for g in groups::<KeyGen>(json) {
                assert_eq!(g.tests.len(), 25);
                for t in &g.tests {
                    let seed: [u8; 32] = unhex(&t.seed).try_into().unwrap();
                    let key = $SigningKey::from_seed(&seed).unwrap();
                    assert_eq!(key.seed(), &seed);
                    assert_eq!(key.verifying_key().as_bytes()[..], unhex(&t.pk)[..]);
                }
            }
        }

        #[test]
        fn sigver() {
            let json = include_str!(
                "../../vectors/nist-acvp/ML-DSA-sigVer-FIPS204/internalProjection.json"
            );
            let mut count = 0;
            for g in groups::<SigVer>(json) {
                // HashML-DSA is not provided.
                if g.pre_hash == "preHash" {
                    continue;
                }
                for t in &g.tests {
                    let pk = $VerifyingKey::from_bytes(&unhex(&t.pk)[..].try_into().unwrap());
                    let sig = unhex(&t.signature)[..].try_into().unwrap();
                    let r = if g.interface == "external" {
                        pk.verify(&unhex(&t.message), &unhex(&t.context), &sig)
                    } else {
                        let mu: [u8; 64] = if g.external_mu {
                            unhex(&t.mu).try_into().unwrap()
                        } else {
                            // `μ = H(H(pk, 64) ‖ M′, 64)`, the message being `M′`.
                            let mut tr = [0u8; 64];
                            Shake256::digest(pk.as_bytes(), &mut tr);
                            let mut h = Shake256::new();
                            h.update(&tr);
                            h.update(&unhex(&t.message));
                            let mut mu = [0u8; 64];
                            h.finalize(&mut mu);
                            mu
                        };
                        pk.verify_internal(&mu, &sig)
                    };
                    let expected = if t.passed {
                        Ok(())
                    } else {
                        Err(Error::InvalidSignature)
                    };
                    assert_eq!(r, expected);
                    count += 1;
                }
            }
            assert_eq!(count, 45);
        }

        /// Signing, hedged and deterministic, gives signatures that verify;
        /// context strings longer than 255 bytes are refused.
        #[test]
        fn sign_verify() {
            let key = $SigningKey::from_seed(&[7; 32]).unwrap();
            let pk = key.verifying_key();
            let sig = key.sign(b"message", b"context").unwrap();
            assert_eq!(pk.verify(b"message", b"context", &sig), Ok(()));
            assert_eq!(
                pk.verify(b"message", b"other", &sig),
                Err(Error::InvalidSignature)
            );
            let sig2 = key.sign_deterministic(b"message", b"").unwrap();
            assert_eq!(sig2, key.sign_deterministic(b"message", b"").unwrap());
            assert_eq!(pk.verify(b"message", b"", &sig2), Ok(()));
            let long = [0u8; 256];
            assert_eq!(key.sign(b"message", &long), Err(Error::ContextTooLong));
            assert_eq!(
                key.sign_deterministic(b"message", &long),
                Err(Error::ContextTooLong)
            );
            assert_eq!(
                pk.verify(b"message", &long, &sig),
                Err(Error::ContextTooLong)
            );
            // A public key is its bytes.
            assert_eq!($VerifyingKey::from_bytes(pk.as_bytes()), pk.clone());
            assert!(format!("{key:?}").starts_with(stringify!($SigningKey)));
            assert!(format!("{pk:?}").starts_with(stringify!($VerifyingKey)));
        }
    };
}

// Used by the parameter sets' files, on the architectures they support.
#[allow(unused_imports)]
pub(crate) use mldsa_tests;
