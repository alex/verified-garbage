//! PBKDF2 (`PbkdfTest` vectors).
#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use core::num::NonZeroU32;

use serde::Deserialize;
use verified_garbage::pbkdf2::pbkdf2_hmac_sha256;

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

/// Every vector must derive exactly its key (the file only has valid
/// vectors).
#[test]
fn pbkdf2_hmac_sha256_vectors() {
    require_vectors!();
    let file = harness::load::<Fields, Case>("pbkdf2_hmacsha256_test.json");
    for (_, test) in file.tests() {
        let c = &test.case;
        assert_eq!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
        let mut dk = vec![0u8; c.dk_len];
        pbkdf2_hmac_sha256(
            &c.password.0,
            &c.salt.0,
            NonZeroU32::new(c.iteration_count).unwrap(),
            &mut dk,
        );
        assert_eq!(dk, c.dk.0, "tcId {}", test.tc_id);
    }
}
