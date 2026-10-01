//! AES-CMAC (`MacTest` vectors, `aes_cmac_test.json`).
//!
//! A valid vector's tag must be the MAC of its message, computed at once,
//! in one `update` and a byte at a time, and `verify` must accept it. An
//! invalid one is either a modified tag, which `verify` must reject, or a
//! key of a length AES does not take, which `new` must reject.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use serde::Deserialize;
use verified_garbage::cmac::InvalidKeyLength;
use verified_garbage::cmac::aes::AesCmac;

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

#[test]
fn cmac_aes() {
    require_vectors!();
    let file = harness::load::<Group, Case>("aes_cmac_test.json");
    let (mut valid, mut modified, mut bad_keys) = (0, 0, 0);
    for (group, test) in file.tests() {
        let Case { key, msg, tag } = &test.case;
        let id = test.tc_id;
        assert_eq!(key.0.len() * 8, group.params.key_size, "tcId {id}");
        assert_eq!(group.params.tag_size, 128, "tcId {id}");
        if !matches!(key.0.len(), 16 | 24 | 32) {
            assert_eq!(test.result, Expectation::Invalid, "tcId {id}");
            let err = AesCmac::new(&key.0).err();
            assert_eq!(err, Some(InvalidKeyLength), "tcId {id}");
            bad_keys += 1;
            continue;
        }
        let full = AesCmac::mac(&key.0, &msg.0).unwrap();
        let mut c = AesCmac::new(&key.0).unwrap();
        c.update(&msg.0);
        assert_eq!(c.finalize(), full, "tcId {id}");
        let mut c = AesCmac::new(&key.0).unwrap();
        for byte in &msg.0 {
            c.update(core::slice::from_ref(byte));
        }
        assert_eq!(c.finalize(), full, "tcId {id}");
        let mut c = AesCmac::new(&key.0).unwrap();
        c.update(&msg.0);
        let ok = c.verify(&tag.0).is_ok();
        if test.result == Expectation::Valid {
            assert!(ok, "tcId {id}");
            assert_eq!(&full[..], &tag.0[..], "tcId {id}");
            valid += 1;
        } else {
            assert_eq!(test.result, Expectation::Invalid, "tcId {id}");
            assert!(!ok, "tcId {id}");
            assert_ne!(&full[..], &tag.0[..], "tcId {id}");
            modified += 1;
        }
    }
    assert_eq!((valid, modified, bad_keys), (63, 243, 5));
}
