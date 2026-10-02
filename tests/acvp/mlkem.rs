//! The ACVP tests of ML-KEM (FIPS 203), for each parameter set: every vector
//! of the key generation and encapsulation tests, and of the encapsulation
//! key check. The decapsulation vectors have expanded decapsulation keys
//! without their seeds, which the API does not accept, so decapsulation is
//! checked with the keys of the key generation vectors: of the ciphertexts
//! that encapsulation gives, and of those ciphertexts changed, which it must
//! reject implicitly (with the key `J(z ‖ c)`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use serde::Deserialize;

#[derive(Deserialize)]
struct File<T> {
    #[serde(rename = "testGroups")]
    groups: Vec<Group<T>>,
}

#[derive(Deserialize)]
struct Group<T> {
    #[serde(rename = "parameterSet")]
    parameter_set: String,
    function: Option<String>,
    tests: Vec<T>,
}

#[derive(Deserialize)]
pub struct KeyGen {
    pub d: String,
    pub z: String,
    pub ek: String,
    pub dk: String,
}

#[derive(Deserialize)]
pub struct EncapDecap {
    pub ek: String,
    #[serde(default)]
    pub m: String,
    #[serde(default)]
    pub c: String,
    #[serde(default)]
    pub k: String,
    #[serde(rename = "testPassed")]
    pub passed: Option<bool>,
}

pub fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

pub fn array<const N: usize>(s: &str) -> [u8; N] {
    unhex(s).try_into().unwrap()
}

/// The tests of the groups of a file for the parameter set `name`, with the
/// function `function` (if any).
fn tests<T: for<'a> Deserialize<'a>>(text: &str, name: &str, function: Option<&str>) -> Vec<T> {
    let file: File<T> = serde_json::from_str(text).unwrap();
    let groups: Vec<_> = file
        .groups
        .into_iter()
        .filter(|g| g.parameter_set == name && g.function.as_deref() == function)
        .map(|g| g.tests)
        .collect();
    assert!(!groups.is_empty());
    groups.into_iter().flatten().collect()
}

/// The key generation vectors of the parameter set `name`.
pub fn keygen_vectors(name: &str) -> Vec<KeyGen> {
    let text =
        include_str!("../../vectors/nist-acvp/ML-KEM-keyGen-FIPS203/internalProjection.json");
    tests(text, name, None)
}

/// The vectors of the parameter set `name` for `function`.
pub fn encap_decap(name: &str, function: &str) -> Vec<EncapDecap> {
    let text =
        include_str!("../../vectors/nist-acvp/ML-KEM-encapDecap-FIPS203/internalProjection.json");
    tests(text, name, Some(function))
}

/// Defines the tests of the parameter set named `$name` (`"ML-KEM-768"`), of
/// the module `verified_garbage::$module` and its key types.
macro_rules! mlkem_tests {
    ($name:literal, verified_garbage::$module:ident, $DecapsulationKey:ident, $EncapsulationKey:ident) => {
        use verified_garbage::hashes::sha3::{Sha3_256, Shake256};
        use verified_garbage::$module::{Error, $DecapsulationKey, $EncapsulationKey};

        use crate::mlkem::{KeyGen, array, encap_decap, keygen_vectors, unhex};

        const EK: usize = $EncapsulationKey::SIZE;
        const CT: usize = $EncapsulationKey::CIPHERTEXT_SIZE;

        /// The key pair of the seed `d ‖ z`.
        fn key(v: &KeyGen) -> $DecapsulationKey {
            let seed: [u8; 64] = [unhex(&v.d), unhex(&v.z)].concat().try_into().unwrap();
            let dk = $DecapsulationKey::from_seed(&seed).unwrap();
            assert_eq!(dk.seed(), &seed);
            dk
        }

        #[test]
        fn key_generation() {
            let vectors = keygen_vectors($name);
            assert_eq!(vectors.len(), 25);
            for v in &vectors {
                let dk = key(v);
                let ek = dk.encapsulation_key().as_bytes();
                assert_eq!(ek[..], unhex(&v.ek));
                // The expanded key is `dk_PKE ‖ ek ‖ H(ek) ‖ z` (`dk_PKE` is
                // 32 bytes shorter than `ek`), which the API keeps private:
                // check its layout against the seed and the key.
                let expanded = unhex(&v.dk);
                let pke = EK - 32;
                assert_eq!(expanded[pke..pke + EK], ek[..]);
                assert_eq!(expanded[pke + EK..pke + EK + 32], Sha3_256::digest(ek));
                assert_eq!(expanded[pke + EK + 32..], dk.seed()[32..]);
            }
        }

        #[test]
        fn encapsulation() {
            let vectors = encap_decap($name, "encapsulation");
            assert_eq!(vectors.len(), 25);
            for v in &vectors {
                let ek = $EncapsulationKey::from_bytes(&array(&v.ek)).unwrap();
                let (k, c) = ek.encapsulate_internal(&array(&v.m)).unwrap();
                assert_eq!(k[..], unhex(&v.k));
                assert_eq!(c[..], unhex(&v.c));
            }
        }

        #[test]
        fn encapsulation_key_check() {
            let vectors = encap_decap($name, "encapsulationKeyCheck");
            assert_eq!(vectors.len(), 10);
            for v in &vectors {
                // Every key of these vectors has the right length.
                let ek: [u8; EK] = array(&v.ek);
                let passed = v.passed.unwrap();
                match $EncapsulationKey::from_bytes(&ek) {
                    Ok(key) => {
                        assert!(passed);
                        assert_eq!(key.as_bytes(), &ek);
                    }
                    Err(e) => {
                        assert!(!passed);
                        assert_eq!(e, Error::InvalidKey);
                    }
                }
            }
        }

        /// Decapsulation of the ciphertexts that encapsulation gives (with
        /// the randomness of the encapsulation vectors), and implicit
        /// rejection of those ciphertexts with a byte changed.
        #[test]
        fn decapsulation() {
            let encaps = encap_decap($name, "encapsulation");
            for (v, e) in keygen_vectors($name).iter().zip(&encaps) {
                let dk = key(v);
                let ek = dk.encapsulation_key();
                let (k, c) = ek.encapsulate_internal(&array(&e.m)).unwrap();
                assert_eq!(dk.decapsulate(&c).unwrap(), k);
                for i in [0, 500, CT - 1] {
                    let mut bad = c;
                    bad[i] ^= 1 << (i % 8);
                    let mut kbar = [0u8; 32];
                    Shake256::digest(&[&unhex(&v.z)[..], &bad[..]].concat(), &mut kbar);
                    assert_eq!(dk.decapsulate(&bad).unwrap(), kbar);
                }
            }
        }

        /// Encapsulation with the operating system's randomness decapsulates
        /// to the same key.
        #[test]
        fn round_trip() {
            let v = &keygen_vectors($name)[0];
            let dk = key(v);
            let copy = $EncapsulationKey::from_bytes(dk.encapsulation_key().as_bytes()).unwrap();
            assert_eq!(&copy, dk.encapsulation_key());
            let (k1, c1) = copy.encapsulate().unwrap();
            let (k2, c2) = copy.encapsulate().unwrap();
            assert_ne!(c1, c2);
            assert_eq!(dk.decapsulate(&c1).unwrap(), k1);
            assert_eq!(dk.decapsulate(&c2).unwrap(), k2);
            assert_eq!(
                format!("{copy:?}"),
                concat!(stringify!($EncapsulationKey), " { .. }")
            );
            assert_eq!(
                format!("{dk:?}"),
                concat!(stringify!($DecapsulationKey), " { .. }")
            );
        }
    };
}

pub(crate) use mlkem_tests;
