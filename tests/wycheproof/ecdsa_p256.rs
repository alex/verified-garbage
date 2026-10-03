//! ECDSA over P-256 with SHA-256 (`EcdsaP1363Verify` vectors of
//! `ecdsa_secp256r1_sha256_p1363_test.json`, signatures as `r ‖ s`).
//!
//! A valid vector must verify, an invalid one must be refused (or, if its
//! signature is not 64 bytes, cannot be passed).

#![cfg(target_arch = "x86_64")]

use serde::Deserialize;
use verified_garbage::ecdsa::{Error, P256, VerifyingKey};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
struct Key {
    curve: String,
    uncompressed: Hex,
}

#[derive(Deserialize)]
struct Group {
    #[serde(rename = "publicKey")]
    public_key: Key,
    sha: String,
}

#[derive(Deserialize)]
struct Case {
    msg: Hex,
    sig: Hex,
}

#[test]
fn ecdsa_secp256r1_sha256_p1363_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ecdsa_secp256r1_sha256_p1363_test.json");
    let (mut verified, mut refused) = (0, 0);
    for (group, test) in file.tests() {
        assert_eq!(group.params.public_key.curve, "secp256r1");
        assert_eq!(group.params.sha, "SHA-256");
        let q: [u8; 65] = group.params.public_key.uncompressed.0[..]
            .try_into()
            .unwrap();
        let key = VerifyingKey::<P256>::from_bytes(&q);
        let Ok(sig) = <[u8; 64]>::try_from(&test.case.sig.0[..]) else {
            assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
            continue;
        };
        let result = key.verify_sha256(&test.case.msg.0, &sig);
        match test.result {
            Expectation::Valid => {
                assert_eq!(result, Ok(()), "tcId {}", test.tc_id);
                verified += 1;
            }
            Expectation::Invalid | Expectation::Acceptable => {
                assert_eq!(result, Err(Error::InvalidSignature), "tcId {}", test.tc_id);
                refused += 1;
            }
        }
    }
    assert!(verified > 0 && refused > 0);
}
