//! ChaCha20, via the ciphertexts of the ChaCha20-Poly1305 (`AeadTest`) vectors.
//!
//! Wycheproof has no vectors for ChaCha20 on its own, but in
//! ChaCha20-Poly1305 (RFC 8439 §2.8) the ciphertext is the plaintext
//! encrypted with ChaCha20 under the key and the 12-byte nonce, starting from
//! block counter 1. So every valid vector with a 12-byte nonce checks the
//! keystream; the tag, and the invalid vectors (which are about the tag or
//! the nonce size), are for a ChaCha20-Poly1305 implementation.

use serde::Deserialize;
use verified_garbage::chacha20::ChaCha20;

use crate::harness::{self, Expectation};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    iv_size: usize,
}

#[derive(Deserialize)]
struct Case {
    key: String,
    iv: String,
    msg: String,
    ct: String,
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn chacha20_poly1305_ciphertexts() {
    require_vectors!();
    let file = harness::load::<Group, Case>("chacha20_poly1305_test.json");
    let mut checked = 0;
    for (group, test) in file.tests() {
        if group.params.iv_size != 96 || test.result != Expectation::Valid {
            continue;
        }
        let key: [u8; 32] = unhex(&test.case.key).try_into().unwrap();
        let mut nonce = [0u8; 16];
        nonce[..4].copy_from_slice(&1u32.to_le_bytes());
        nonce[4..].copy_from_slice(&unhex(&test.case.iv));
        let mut data = unhex(&test.case.msg);
        ChaCha20::new(&key, &nonce).apply_keystream(&mut data);
        assert_eq!(data, unhex(&test.case.ct), "tcId {}", test.tc_id);
        checked += 1;
    }
    assert!(checked > 0);
}
