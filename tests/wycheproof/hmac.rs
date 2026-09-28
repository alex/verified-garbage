//! HMAC (`MacTest` vectors).

use serde::Deserialize;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hmac::{Hmac, HmacHash};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

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

/// Checks every vector of `name`: a (possibly truncated) tag computed with
/// the key must equal the expected one exactly when the test is valid.
fn check<H: HmacHash>(name: &str) {
    let file = harness::load::<Group, Case>(name);
    for (group, test) in file.tests() {
        let Case { key, msg, tag } = &test.case;
        assert_eq!(key.0.len() * 8, group.params.key_size);
        assert!(group.params.tag_size <= H::OUTPUT_SIZE * 8);
        // Two ways of computing the MAC: at once, and one byte at a time
        // with each implementation this CPU can run (the best one, and the
        // one for the baseline ISA).
        let full = Hmac::<H>::mac(&key.0, &msg.0);
        for mask in [u32::MAX, 0] {
            let mut h = Hmac::<H>::__with_features(&key.0, mask);
            for byte in &msg.0 {
                h.update(core::slice::from_ref(byte));
            }
            assert_eq!(h.finalize().as_ref(), full.as_ref());
        }
        let computed = &full.as_ref()[..group.params.tag_size / 8];
        if test.result == Expectation::Valid {
            assert_eq!(computed, &tag.0[..], "tcId {}", test.tc_id);
        } else {
            assert_eq!(test.result, Expectation::Invalid);
            assert_ne!(computed, &tag.0[..], "tcId {}", test.tc_id);
        }
    }
}

#[test]
fn hmac_sha256() {
    require_vectors!();
    check::<Sha256>("hmac_sha256_test.json");
}
