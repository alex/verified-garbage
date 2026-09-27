//! PBKDF2 (`PbkdfTest` vectors).

use core::num::NonZeroU32;

use serde::Deserialize;
use verified_garbage::hmac::HmacHash;
use verified_garbage::pbkdf2::pbkdf2_hmac;
use verified_garbage::sha256::Sha256;

use crate::harness::{self, Expectation, Fields, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Case {
    password: Hex,
    salt: Hex,
    iteration_count: u32,
    dk_len: usize,
    dk: Hex,
}

/// Every vector of `name` must derive exactly its key (the files only have
/// valid vectors).
fn check<H: HmacHash>(name: &str) {
    let file = harness::load::<Fields, Case>(name);
    for (_, test) in file.tests() {
        let c = &test.case;
        assert_eq!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
        let mut dk = vec![0u8; c.dk_len];
        pbkdf2_hmac::<H>(
            &c.password.0,
            &c.salt.0,
            NonZeroU32::new(c.iteration_count).unwrap(),
            &mut dk,
        );
        assert_eq!(dk, c.dk.0, "tcId {}", test.tc_id);
    }
}

#[test]
fn pbkdf2_hmac_sha256() {
    require_vectors!();
    check::<Sha256>("pbkdf2_hmacsha256_test.json");
}
