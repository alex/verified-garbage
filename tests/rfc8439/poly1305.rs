//! Poly1305: the vectors of Appendix A.3, each checked in one call, split
//! into two pieces at every position, and a byte at a time.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::poly1305::Poly1305;

use super::vectors;

/// A Poly1305 test vector: the key, the message and the tag.
struct Vector {
    key: [u8; 32],
    msg: Vec<u8>,
    tag: Vec<u8>,
}

/// The vectors of Appendix A.3. The first four are hex dumps labelled
/// "One-time Poly1305 Key", "Text to MAC" and "Tag"; the others are rows of
/// hex labelled "R", "S", "data" and "tag".
fn poly1305_vectors() -> Vec<Vector> {
    let vs = vectors("A.3.", "A.4.");
    vs.iter()
        .map(|v| {
            let (key, msg, tag) = if v.has("R") {
                (
                    [v.get("R"), v.get("S")].concat(),
                    v.get("data"),
                    v.get("tag"),
                )
            } else {
                let key = v.get("One-time Poly1305 Key").to_vec();
                (key, v.get("Text to MAC"), v.get("Tag"))
            };
            Vector {
                key: key[..].try_into().unwrap(),
                msg: msg.to_vec(),
                tag: tag.to_vec(),
            }
        })
        .collect()
}

#[test]
fn rfc8439_poly1305() {
    let vs = poly1305_vectors();
    let lens: Vec<usize> = vs.iter().map(|v| v.msg.len()).collect();
    assert_eq!(lens, [64, 375, 375, 127, 16, 16, 48, 48, 16, 64, 48]);
    for v in &vs {
        assert_eq!(Poly1305::mac(&v.key, &v.msg)[..], v.tag[..]);
    }
}

/// Every vector, absorbed in two pieces split at every position, and a byte
/// at a time.
#[test]
fn rfc8439_poly1305_split() {
    for v in &poly1305_vectors() {
        for i in 0..=v.msg.len() {
            let mut p = Poly1305::new(&v.key);
            p.update(&v.msg[..i]);
            p.update(&v.msg[i..]);
            assert_eq!(p.finalize()[..], v.tag[..]);
        }
        let mut p = Poly1305::new(&v.key);
        for byte in &v.msg {
            p.update(core::slice::from_ref(byte));
        }
        assert_eq!(p.finalize()[..], v.tag[..]);
    }
}
