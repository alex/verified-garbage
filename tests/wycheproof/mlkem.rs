//! The Wycheproof tests of ML-KEM, for each parameter set: the `MLKEMKeyGen`
//! vectors of `mlkem_*_keygen_seed_test.json`, the `MLKEMEncapsTest`
//! vectors of `mlkem_*_encaps_test.json` and the `MLKEMTest` vectors of
//! `mlkem_*_test.json`.
//!
//! The API keeps a decapsulation key as its seed, so the vectors of
//! `mlkem_*_semi_expanded_decaps_test.json`, which give expanded
//! decapsulation keys, do not apply; the decapsulation vectors of
//! `mlkem_*_test.json` give seeds. The invalid vectors are seeds,
//! ciphertexts and encapsulation keys of the wrong length, which the types
//! do not represent, and encapsulation keys that fail the check of FIPS 203
//! §7.2, which `EncapsulationKey*::from_bytes` rejects.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use serde::Deserialize;

use crate::harness::Hex;

#[derive(Deserialize)]
pub struct KeyGen {
    pub seed: Hex,
    pub ek: Hex,
    pub dk: Hex,
}

#[derive(Deserialize)]
pub struct Encaps {
    pub ek: Hex,
    pub m: Hex,
    pub c: Hex,
    #[serde(rename = "K")]
    pub k: Hex,
}

#[derive(Deserialize)]
pub struct Decaps {
    pub seed: Hex,
    #[serde(default)]
    pub ek: Option<Hex>,
    pub c: Hex,
    #[serde(rename = "K")]
    pub k: Hex,
}

/// Defines the tests of the parameter set `$n` (`"768"`), of the module
/// `verified_garbage::$module` and its key types.
macro_rules! mlkem_tests {
    ($n:literal, verified_garbage::$module:ident, $DecapsulationKey:ident, $EncapsulationKey:ident) => {
        use verified_garbage::hashes::sha3::Sha3_256;
        use verified_garbage::$module::{Error, $DecapsulationKey, $EncapsulationKey};

        use crate::harness::{self, Expectation, Fields};
        use crate::mlkem::{Decaps, Encaps, KeyGen};
        use crate::require_vectors;

        const EK: usize = $EncapsulationKey::SIZE;
        const CT: usize = $EncapsulationKey::CIPHERTEXT_SIZE;

        #[test]
        fn keygen_seed() {
            require_vectors!();
            let file =
                harness::load::<Fields, KeyGen>(concat!("mlkem_", $n, "_keygen_seed_test.json"));
            for (_, test) in file.tests() {
                let c = &test.case;
                assert_eq!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
                let dk = $DecapsulationKey::from_seed(&c.seed.0[..].try_into().unwrap()).unwrap();
                let ek = dk.encapsulation_key().as_bytes();
                assert_eq!(ek[..], c.ek.0, "tcId {}", test.tc_id);
                // The expanded key is `dk_PKE ‖ ek ‖ H(ek) ‖ z` (`dk_PKE` is
                // 32 bytes shorter than `ek`), which the API keeps private:
                // check its layout against the seed and the key.
                let pke = EK - 32;
                assert_eq!(c.dk.0[pke..pke + EK], ek[..], "tcId {}", test.tc_id);
                let h = Sha3_256::digest(ek);
                assert_eq!(c.dk.0[pke + EK..pke + EK + 32], h, "tcId {}", test.tc_id);
                assert_eq!(
                    c.dk.0[pke + EK + 32..],
                    dk.seed()[32..],
                    "tcId {}",
                    test.tc_id
                );
            }
        }

        #[test]
        fn encaps() {
            require_vectors!();
            let file = harness::load::<Fields, Encaps>(concat!("mlkem_", $n, "_encaps_test.json"));
            for (_, test) in file.tests() {
                let c = &test.case;
                let m: [u8; 32] = c.m.0[..].try_into().unwrap();
                let key =
                    <[u8; EK]>::try_from(&c.ek.0[..]).map(|ek| $EncapsulationKey::from_bytes(&ek));
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
            let file = harness::load::<Fields, Decaps>(concat!("mlkem_", $n, "_test.json"));
            for (_, test) in file.tests() {
                let c = &test.case;
                let seed = <[u8; 64]>::try_from(&c.seed.0[..]);
                let ct = <[u8; CT]>::try_from(&c.c.0[..]);
                match (seed, ct) {
                    (Ok(seed), Ok(ct)) => {
                        assert_eq!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
                        let dk = $DecapsulationKey::from_seed(&seed).unwrap();
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
    };
}

pub(crate) use mlkem_tests;
