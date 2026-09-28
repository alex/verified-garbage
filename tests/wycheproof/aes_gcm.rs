//! AES-GCM (`AeadTest` vectors, `aes_gcm_test.json`).
//!
//! A valid vector must encrypt to exactly its ciphertext and tag, and
//! decrypt back, both at once and streaming. An invalid vector must be
//! rejected: by decryption (a modified tag, ciphertext or additional data),
//! or already by the nonce check (an empty nonce).

#![cfg(target_arch = "x86_64")]

use serde::Deserialize;
use verified_garbage::aes_gcm::{AesGcm, AesGcmStream, Direction, Error};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    tag_size: usize,
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

/// Masks that between them select every implementation this CPU can run.
const MASKS: [u32; 2] = [u32::MAX, 0];

/// Streaming decryption of `c`: the plaintext, if the tag matched.
fn stream_decrypt(c: &Case, mask: u32) -> Result<Vec<u8>, Error> {
    let mut d = AesGcmStream::__with_features(&c.key.0, &c.iv.0, Direction::Decrypt, mask)?;
    d.update_aad(&c.aad.0)?;
    let mut buf = c.ct.0.clone();
    d.update(&mut buf)?;
    d.set_tag(&c.tag.0)?;
    d.finalize()?;
    Ok(buf)
}

#[test]
fn aes_gcm() {
    require_vectors!();
    let file = harness::load::<Group, Case>("aes_gcm_test.json");
    let (mut valid, mut invalid) = (0, 0);
    let cases = file.tests().flat_map(|t| MASKS.map(|m| (t, m)));
    for ((group, test), mask) in cases {
        let c = &test.case;
        let id = test.tc_id;
        assert_eq!(group.params.tag_size, 8 * c.tag.0.len(), "tcId {id}");
        let key = AesGcm::__with_features(&c.key.0, mask).unwrap();
        let mut buf = c.ct.0.clone();
        let decrypted = key.decrypt(&c.iv.0, &c.aad.0, &mut buf, &c.tag.0);
        match test.result {
            Expectation::Valid => {
                decrypted.unwrap_or_else(|e| panic!("tcId {id}: {e:?}"));
                assert_eq!(buf, c.msg.0, "tcId {id}");
                let mut buf = c.msg.0.clone();
                let tag = key.encrypt(&c.iv.0, &c.aad.0, &mut buf).unwrap();
                assert_eq!(buf, c.ct.0, "tcId {id}");
                assert_eq!(tag[..], c.tag.0, "tcId {id}");

                let mut e =
                    AesGcmStream::__with_features(&c.key.0, &c.iv.0, Direction::Encrypt, mask)
                        .unwrap();
                e.update_aad(&c.aad.0).unwrap();
                let mut buf = c.msg.0.clone();
                e.update(&mut buf).unwrap();
                assert_eq!(buf, c.ct.0, "tcId {id}");
                assert_eq!(e.finalize(), Ok(tag), "tcId {id}");
                assert_eq!(stream_decrypt(c, mask), Ok(c.msg.0.clone()), "tcId {id}");
                valid += 1;
            }
            // The file has no acceptable vectors.
            _ => {
                assert!(matches!(test.result, Expectation::Invalid), "tcId {id}");
                assert!(decrypted.is_err(), "tcId {id}");
                assert_eq!(buf, c.ct.0, "tcId {id}: rejected ciphertext was modified");
                invalid += 1;
            }
        }
    }
    assert!(valid > 0 && invalid > 0);
}
