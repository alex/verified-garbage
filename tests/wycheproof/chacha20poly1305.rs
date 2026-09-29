//! ChaCha20-Poly1305 (`AeadTest` vectors).
//!
//! The API takes the 12-byte nonce of RFC 8439, so the groups with other
//! nonce sizes (all of whose vectors are invalid) are checked to be
//! unrepresentable rather than run.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use serde::Deserialize;
use verified_garbage::chacha20poly1305::{ChaCha20Poly1305, InvalidTag};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    iv_size: usize,
}

#[derive(Deserialize)]
struct Case {
    key: Hex,
    iv: Hex,
    aad: Hex,
    msg: Hex,
    ct: Hex,
    tag: Hex,
}

#[test]
fn chacha20_poly1305() {
    require_vectors!();
    let file = harness::load::<Group, Case>("chacha20_poly1305_test.json");
    let mut checked = 0;
    for (group, test) in file.tests() {
        let c = &test.case;
        if group.params.iv_size != 96 {
            assert_ne!(c.iv.0.len(), 12);
            assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
            continue;
        }
        let aead = ChaCha20Poly1305::new(&c.key.0[..].try_into().unwrap());
        let nonce: [u8; 12] = c.iv.0[..].try_into().unwrap();
        let tag: [u8; 16] = c.tag.0[..].try_into().unwrap();
        let mut data = c.ct.0.clone();
        let opened = aead.decrypt_in_place(&nonce, &c.aad.0, &mut data, &tag);
        if test.result == Expectation::Valid {
            assert_eq!(opened, Ok(()), "tcId {}", test.tc_id);
            assert_eq!(data, c.msg.0, "tcId {}", test.tc_id);
            let mut data = c.msg.0.clone();
            let sealed = aead.encrypt_in_place(&nonce, &c.aad.0, &mut data);
            assert_eq!(data, c.ct.0, "tcId {}", test.tc_id);
            assert_eq!(sealed, tag, "tcId {}", test.tc_id);
        } else {
            // There are no acceptable vectors.
            assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
            assert_eq!(opened, Err(InvalidTag), "tcId {}", test.tc_id);
            assert!(data.iter().all(|&b| b == 0), "tcId {}", test.tc_id);
        }
        checked += 1;
    }
    assert!(checked > 0);
}
