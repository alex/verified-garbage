//! All pure Ed25519 verification cases in Wycheproof's ed25519_test.json.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86"))]

use serde::Deserialize;
use verified_garbage::ed25519::{Error, VerifyingKey};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
struct PublicKey {
    curve: String,
    pk: Hex,
}

#[derive(Deserialize)]
struct Group {
    #[serde(rename = "publicKey")]
    public_key: PublicKey,
}

#[derive(Deserialize)]
struct Case {
    msg: Hex,
    sig: Hex,
}

#[test]
fn ed25519_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ed25519_test.json");
    let mut checked = 0;
    for (group, test) in file.tests() {
        assert_eq!(group.params.public_key.curve, "edwards25519");
        let public: [u8; 32] = group.params.public_key.pk.0.clone().try_into().unwrap();
        let key = VerifyingKey::from_bytes(&public);
        assert_ne!(test.result, Expectation::Acceptable, "tcId {}", test.tc_id);
        let expected = if test.result == Expectation::Valid {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        };
        let actual = key.verify(&test.case.msg.0, &test.case.sig.0);
        assert_eq!(actual, expected, "tcId {}", test.tc_id);
        checked += 1;
    }
    assert!(checked > 0);
}
