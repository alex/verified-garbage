//! AES-GCM (`AeadTest` vectors, `aes_gcm_test.json`).
//!
//! A valid vector must encrypt to exactly its ciphertext and tag, and
//! decrypt back, both at once and streaming. An invalid vector must be
//! rejected: by decryption (a modified tag, ciphertext or additional data),
//! or already by the nonce check (an empty nonce).
//!
//! Every vector has a full 16-byte tag; the CAVP vectors
//! (`tests/cavp/aes_gcm.rs`) test truncated ones.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

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

/// The tag of `c`, which is 16 bytes long.
fn tag(c: &Case) -> &[u8; 16] {
    c.tag.0.as_slice().try_into().unwrap()
}

/// Streaming decryption of `c`: the plaintext, if the tag matched.
fn stream_decrypt(c: &Case) -> Result<Vec<u8>, Error> {
    let mut d = AesGcmStream::new(&c.key.0, &c.iv.0, Direction::Decrypt)?;
    d.update_aad(&c.aad.0)?;
    let mut buf = c.ct.0.clone();
    d.update(&mut buf)?;
    d.set_tag(tag(c))?;
    d.finalize()?;
    Ok(buf)
}

#[test]
fn aes_gcm() {
    require_vectors!();
    let file = harness::load::<Group, Case>("aes_gcm_test.json");
    let (mut valid, mut invalid) = (0, 0);
    for (group, test) in file.tests() {
        let c = &test.case;
        let id = test.tc_id;
        assert_eq!(group.params.tag_size, 8 * c.tag.0.len(), "tcId {id}");
        assert_eq!(group.params.tag_size, 128, "tcId {id}");
        let key = AesGcm::new(&c.key.0).unwrap();
        let mut buf = c.ct.0.clone();
        let decrypted = key.decrypt_in_place(&c.iv.0, &c.aad.0, &mut buf, tag(c));
        match test.result {
            Expectation::Valid => {
                decrypted.unwrap_or_else(|e| panic!("tcId {id}: {e:?}"));
                assert_eq!(buf, c.msg.0, "tcId {id}");
                let mut buf = c.msg.0.clone();
                let tag = key.encrypt_in_place(&c.iv.0, &c.aad.0, &mut buf).unwrap();
                assert_eq!(buf, c.ct.0, "tcId {id}");
                assert_eq!(tag[..], c.tag.0, "tcId {id}");

                let mut e = AesGcmStream::new(&c.key.0, &c.iv.0, Direction::Encrypt).unwrap();
                e.update_aad(&c.aad.0).unwrap();
                let mut buf = c.msg.0.clone();
                e.update(&mut buf).unwrap();
                assert_eq!(buf, c.ct.0, "tcId {id}");
                assert_eq!(e.finalize(), Ok(tag), "tcId {id}");
                assert_eq!(stream_decrypt(c), Ok(c.msg.0.clone()), "tcId {id}");
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
