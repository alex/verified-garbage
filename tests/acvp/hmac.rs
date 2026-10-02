//! HMAC (`HMAC-SHA2-*` vector sets): the checks every hash function's tests
//! (`hmac_<hash>.rs`) run. Their keys go up to 256 bytes, so they include
//! keys longer than a block, which `init` replaces by their digest.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use serde::Deserialize;
use verified_garbage::hmac::{Hmac, HmacHash};

#[derive(Deserialize)]
struct File {
    #[serde(rename = "testGroups")]
    groups: Vec<Group>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    key_len: usize,
    msg_len: usize,
    mac_len: usize,
    tests: Vec<Case>,
}

#[derive(Deserialize)]
struct Case {
    key: String,
    msg: String,
    mac: String,
}

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// Checks every vector of the vendored file `json` with `Hmac<H>`: the MAC,
/// truncated to the vector's length, is the expected one, and `verify`
/// accepts it when it is whole. Some of the keys are longer than a block.
pub(crate) fn check<H: HmacHash>(json: &str) {
    let file: File = serde_json::from_str(json).unwrap();
    let mut long = 0;
    for group in &file.groups {
        assert!(group.mac_len <= H::OUTPUT_SIZE * 8);
        for case in &group.tests {
            let (key, msg, mac) = (unhex(&case.key), unhex(&case.msg), unhex(&case.mac));
            assert_eq!(key.len() * 8, group.key_len);
            assert_eq!(msg.len() * 8, group.msg_len);
            assert_eq!(mac.len() * 8, group.mac_len);
            let full = Hmac::<H>::mac(&key, &msg);
            assert_eq!(&full.as_ref()[..mac.len()], &mac[..]);
            let mut h = Hmac::<H>::new(&key);
            h.update(&msg);
            assert_eq!(h.verify(&mac).is_ok(), mac.len() == H::OUTPUT_SIZE);
            if key.len() > H::BLOCK_SIZE {
                long += 1;
            }
        }
    }
    assert!(long > 0);
}
