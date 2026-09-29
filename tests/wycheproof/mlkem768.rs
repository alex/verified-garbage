//! ML-KEM-768 (`MLKEMKeyGen`, `MLKEMEncapsTest` and `MLKEMTest` vectors).
//!
//! The API keeps a decapsulation key as its seed, so the vectors of
//! `mlkem_768_semi_expanded_decaps_test.json`, which give expanded
//! decapsulation keys, do not apply; the decapsulation vectors of
//! `mlkem_768_test.json` give seeds. The invalid vectors are seeds,
//! ciphertexts and encapsulation keys of the wrong length, which the types
//! do not represent, and encapsulation keys that fail the check of FIPS 203
//! §7.2, which `EncapsulationKey768::from_bytes` rejects.

#![cfg(any(target_arch = "x86_64", target_arch = "x86"))]

use serde::Deserialize;
use verified_garbage::hashes::sha3::Sha3_256;
use verified_garbage::mlkem768::{DecapsulationKey768, EncapsulationKey768, Error};

use crate::harness::{self, Expectation, Fields, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
struct KeyGen {
    seed: Hex,
    ek: Hex,
    dk: Hex,
}

#[derive(Deserialize)]
struct Encaps {
    ek: Hex,
    m: Hex,
    c: Hex,
    #[serde(rename = "K")]
    k: Hex,
}

#[derive(Deserialize)]
struct Decaps {
    seed: Hex,
    #[serde(default)]
    ek: Option<Hex>,
    c: Hex,
    #[serde(rename = "K")]
    k: Hex,
}

#[test]
fn keygen_seed() {
    require_vectors!();
    let file = harness::load::<Fields, KeyGen>("mlkem_768_keygen_seed_test.json");
    for (_, test) in file.tests() {
        let c = &test.case;
        assert_eq!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
        let dk = DecapsulationKey768::from_seed(&c.seed.0[..].try_into().unwrap()).unwrap();
        let ek = dk.encapsulation_key().as_bytes();
        assert_eq!(ek[..], c.ek.0, "tcId {}", test.tc_id);
        // The expanded key is `dk_PKE ‖ ek ‖ H(ek) ‖ z`, which the API keeps
        // private: check its layout against the seed and the key.
        assert_eq!(c.dk.0[1152..2336], ek[..], "tcId {}", test.tc_id);
        let h = Sha3_256::digest(ek);
        assert_eq!(c.dk.0[2336..2368], h, "tcId {}", test.tc_id);
        assert_eq!(c.dk.0[2368..], dk.seed()[32..], "tcId {}", test.tc_id);
    }
}

#[test]
fn encaps() {
    require_vectors!();
    let file = harness::load::<Fields, Encaps>("mlkem_768_encaps_test.json");
    for (_, test) in file.tests() {
        let c = &test.case;
        let m: [u8; 32] = c.m.0[..].try_into().unwrap();
        let key =
            <[u8; 1184]>::try_from(&c.ek.0[..]).map(|ek| EncapsulationKey768::from_bytes(&ek));
        match test.result {
            Expectation::Valid => {
                let (k, ct) = key.unwrap().unwrap().encapsulate_internal(&m).unwrap();
                assert_eq!(k[..], c.k.0, "tcId {}", test.tc_id);
                assert_eq!(ct[..], c.c.0, "tcId {}", test.tc_id);
            }
            _ => {
                assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
                if let Ok(key) = key {
                    assert_eq!(key.err(), Some(Error::InvalidKey), "tcId {}", test.tc_id);
                }
            }
        }
    }
}

#[test]
fn decaps() {
    require_vectors!();
    let file = harness::load::<Fields, Decaps>("mlkem_768_test.json");
    for (_, test) in file.tests() {
        let c = &test.case;
        let seed = <[u8; 64]>::try_from(&c.seed.0[..]);
        let ct = <[u8; 1088]>::try_from(&c.c.0[..]);
        match (seed, ct) {
            (Ok(seed), Ok(ct)) => {
                assert_eq!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
                let dk = DecapsulationKey768::from_seed(&seed).unwrap();
                // Every valid test gives the encapsulation key.
                let ek = c.ek.as_ref().unwrap();
                let got = dk.encapsulation_key().as_bytes();
                assert_eq!(got[..], ek.0, "tcId {}", test.tc_id);
                let k = dk.decapsulate(&ct).unwrap();
                assert_eq!(k[..], c.k.0, "tcId {}", test.tc_id);
            }
            _ => assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id),
        }
    }
}
