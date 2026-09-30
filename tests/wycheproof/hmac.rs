//! HMAC (`MacTest` vectors): the checks every hash function's tests
//! (`hmac_<hash>.rs`) run.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use serde::Deserialize;
use verified_garbage::hmac::{Hmac, HmacHash};

use crate::harness::{self, Expectation, Hex};

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    key_size: usize,
    tag_size: usize,
}

#[derive(Deserialize)]
struct Case {
    key: Hex,
    msg: Hex,
    tag: Hex,
}

/// Checks every vector of `name` with `Hmac<H>`, whose `new` is passed in:
/// a (possibly truncated) tag computed with the key must equal the expected
/// one exactly when the test is valid.
pub(crate) fn check<H: HmacHash>(name: &str, new: fn(&[u8]) -> Hmac<H>) {
    let file = harness::load::<Group, Case>(name);
    for (group, test) in file.tests() {
        let Case { key, msg, tag } = &test.case;
        assert_eq!(key.0.len() * 8, group.params.key_size);
        assert!(group.params.tag_size <= H::OUTPUT_SIZE * 8);
        // Three ways of computing the MAC: at once, in one `update`, and one
        // byte at a time.
        let full = Hmac::<H>::mac(&key.0, &msg.0);
        let mut h = new(&key.0);
        h.update(&msg.0);
        assert_eq!(h.finalize().as_ref(), full.as_ref());
        let mut h = new(&key.0);
        for byte in &msg.0 {
            h.update(core::slice::from_ref(byte));
        }
        assert_eq!(h.finalize().as_ref(), full.as_ref());
        // `verify` takes only whole MACs: it accepts the expected tag when
        // the test is valid and is not truncated, and rejects it otherwise.
        let mut h = new(&key.0);
        h.update(&msg.0);
        let whole = group.params.tag_size == H::OUTPUT_SIZE * 8;
        assert_eq!(
            h.verify(&tag.0).is_ok(),
            whole && test.result == Expectation::Valid,
            "tcId {}",
            test.tc_id
        );
        let computed = &full.as_ref()[..group.params.tag_size / 8];
        if test.result == Expectation::Valid {
            assert_eq!(computed, &tag.0[..], "tcId {}", test.tc_id);
        } else {
            assert_eq!(test.result, Expectation::Invalid);
            assert_ne!(computed, &tag.0[..], "tcId {}", test.tc_id);
        }
    }
}
