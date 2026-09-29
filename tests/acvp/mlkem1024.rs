//! ML-KEM-1024 (FIPS 203): every ML-KEM-1024 vector of the key generation and
//! encapsulation tests, and of the encapsulation key check. The
//! decapsulation vectors have expanded decapsulation keys without their
//! seeds, which the API does not accept, so decapsulation is checked with
//! the keys of the key generation vectors: of the ciphertexts that
//! encapsulation gives, and of those ciphertexts changed, which it must
//! reject implicitly (with the key `J(z ‖ c)`).

#![cfg(any(target_arch = "x86_64", target_arch = "x86"))]

use serde::Deserialize;
use verified_garbage::hashes::sha3::{Sha3_256, Shake256};
use verified_garbage::mlkem1024::{DecapsulationKey1024, EncapsulationKey1024, Error};

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
struct KeyGen {
    d: String,
    z: String,
    ek: String,
    dk: String,
}

#[derive(Deserialize)]
struct EncapDecap {
    ek: String,
    #[serde(default)]
    m: String,
    #[serde(default)]
    c: String,
    #[serde(default)]
    k: String,
    #[serde(rename = "testPassed")]
    passed: Option<bool>,
}

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn array<const N: usize>(s: &str) -> [u8; N] {
    unhex(s).try_into().unwrap()
}

/// The ML-KEM-1024 groups of a file, with the function `function` (if any).
fn groups<T: for<'a> Deserialize<'a>>(text: &str, function: Option<&str>) -> Vec<Vec<T>> {
    let file: File<T> = serde_json::from_str(text).unwrap();
    let groups: Vec<_> = file
        .groups
        .into_iter()
        .filter(|g| g.parameter_set == "ML-KEM-1024" && g.function.as_deref() == function)
        .map(|g| g.tests)
        .collect();
    assert!(!groups.is_empty());
    groups
}

fn keygen_vectors() -> Vec<KeyGen> {
    let text =
        include_str!("../../vectors/nist-acvp/ML-KEM-keyGen-FIPS203/internalProjection.json");
    groups(text, None).into_iter().flatten().collect()
}

fn encap_decap(function: &str) -> Vec<EncapDecap> {
    let text =
        include_str!("../../vectors/nist-acvp/ML-KEM-encapDecap-FIPS203/internalProjection.json");
    groups(text, Some(function)).into_iter().flatten().collect()
}

/// The key pair of the seed `d ‖ z`.
fn key(v: &KeyGen) -> DecapsulationKey1024 {
    let seed: [u8; 64] = [unhex(&v.d), unhex(&v.z)].concat().try_into().unwrap();
    let dk = DecapsulationKey1024::from_seed(&seed).unwrap();
    assert_eq!(dk.seed(), &seed);
    dk
}

#[test]
fn key_generation() {
    let vectors = keygen_vectors();
    assert_eq!(vectors.len(), 25);
    for v in &vectors {
        let dk = key(v);
        let ek = dk.encapsulation_key().as_bytes();
        assert_eq!(ek[..], unhex(&v.ek));
        // The expanded key is `dk_PKE ‖ ek ‖ H(ek) ‖ z`, which the API keeps
        // private: check its layout against the seed and the key.
        let expanded = unhex(&v.dk);
        assert_eq!(expanded[1536..3104], ek[..]);
        assert_eq!(expanded[3104..3136], Sha3_256::digest(ek));
        assert_eq!(expanded[3136..], dk.seed()[32..]);
    }
}

#[test]
fn encapsulation() {
    let vectors = encap_decap("encapsulation");
    assert_eq!(vectors.len(), 25);
    for v in &vectors {
        let ek = EncapsulationKey1024::from_bytes(&array(&v.ek)).unwrap();
        let (k, c) = ek.encapsulate_internal(&array(&v.m)).unwrap();
        assert_eq!(k[..], unhex(&v.k));
        assert_eq!(c[..], unhex(&v.c));
    }
}

#[test]
fn encapsulation_key_check() {
    let vectors = encap_decap("encapsulationKeyCheck");
    assert_eq!(vectors.len(), 10);
    for v in &vectors {
        // Every key of these vectors has the right length.
        let ek: [u8; 1568] = array(&v.ek);
        let passed = v.passed.unwrap();
        match EncapsulationKey1024::from_bytes(&ek) {
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

/// Decapsulation of the ciphertexts that encapsulation gives (with the
/// randomness of the encapsulation vectors), and implicit rejection of
/// those ciphertexts with a byte changed.
#[test]
fn decapsulation() {
    let encaps = encap_decap("encapsulation");
    for (v, e) in keygen_vectors().iter().zip(&encaps) {
        let dk = key(v);
        let ek = dk.encapsulation_key();
        let (k, c) = ek.encapsulate_internal(&array(&e.m)).unwrap();
        assert_eq!(dk.decapsulate(&c).unwrap(), k);
        for i in [0, 500, 1567] {
            let mut bad = c;
            bad[i] ^= 1 << (i % 8);
            let mut kbar = [0u8; 32];
            Shake256::digest(&[&unhex(&v.z)[..], &bad[..]].concat(), &mut kbar);
            assert_eq!(dk.decapsulate(&bad).unwrap(), kbar);
        }
    }
}

/// Encapsulation with the operating system's randomness decapsulates to the
/// same key.
#[test]
fn round_trip() {
    let v = &keygen_vectors()[0];
    let dk = key(v);
    let copy = EncapsulationKey1024::from_bytes(dk.encapsulation_key().as_bytes()).unwrap();
    assert_eq!(&copy, dk.encapsulation_key());
    let (k1, c1) = copy.encapsulate().unwrap();
    let (k2, c2) = copy.encapsulate().unwrap();
    assert_ne!(c1, c2);
    assert_eq!(dk.decapsulate(&c1).unwrap(), k1);
    assert_eq!(dk.decapsulate(&c2).unwrap(), k2);
    assert_eq!(format!("{copy:?}"), "EncapsulationKey1024 { .. }");
    assert_eq!(format!("{dk:?}"), "DecapsulationKey1024 { .. }");
}
