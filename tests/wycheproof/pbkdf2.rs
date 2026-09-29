//! PBKDF2 (`PbkdfTest` vectors): the checks every hash function's tests
//! (`pbkdf2_<hash>.rs`) run.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use core::num::NonZeroU32;

use serde::Deserialize;

use crate::harness::{self, Expectation, Fields, Hex};

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
/// valid vectors), with `derive`.
pub(crate) fn check_with(name: &str, derive: fn(&[u8], &[u8], NonZeroU32, &mut [u8])) {
    let file = harness::load::<Fields, Case>(name);
    for (_, test) in file.tests() {
        let c = &test.case;
        assert_eq!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
        let mut dk = vec![0u8; c.dk_len];
        derive(
            &c.password.0,
            &c.salt.0,
            NonZeroU32::new(c.iteration_count).unwrap(),
            &mut dk,
        );
        assert_eq!(dk, c.dk.0, "tcId {}", test.tc_id);
    }
}
