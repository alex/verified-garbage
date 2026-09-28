//! The Poly1305 test vectors of RFC 8439 (Appendix A.3).
//!
//! The RFC is vendored under `vectors/rfc8439/` (see `vectors/sources.toml`
//! for where it comes from) and compiled into the test binary, so these tests
//! always run. Every vector is checked in one call, split into two pieces at
//! every position, and a byte at a time.

#![cfg(any(target_arch = "x86_64", target_arch = "x86"))]

use verified_garbage::poly1305::Poly1305;

/// A Poly1305 test vector: the key, the message and the tag.
struct Vector {
    key: Vec<u8>,
    msg: Vec<u8>,
    tag: Vec<u8>,
}

/// The bytes of a hex dump row (`000  00 01 …  ascii`): the offset, then up
/// to 16 bytes in the 47 columns before the text.
fn dump_row(line: &str) -> Option<Vec<u8>> {
    let (offset, rest) = line.split_at_checked(3)?;
    if !offset.bytes().all(|b| b.is_ascii_digit()) || !rest.starts_with("  ") {
        return None;
    }
    let hex = rest[2..].get(..47).unwrap_or(&rest[2..]);
    hex.split_whitespace().map(byte).collect()
}

/// The bytes of a row of 16 bytes in hex (`FF FF …`).
fn plain_row(line: &str) -> Option<Vec<u8>> {
    let bytes: Option<Vec<u8>> = line.split_whitespace().map(byte).collect();
    bytes.filter(|b| b.len() == 16)
}

fn byte(s: &str) -> Option<u8> {
    (s.len() == 2).then(|| u8::from_str_radix(s, 16).ok())?
}

/// The vectors of Appendix A.3. The first four are hex dumps labelled "One-time
/// Poly1305 Key", "Text to MAC" and "Tag"; the others are rows of hex labelled
/// "R", "S", "data" and "tag". Page breaks and prose are skipped: only rows of
/// hex after a label are data.
fn vectors() -> Vec<Vector> {
    let text = include_str!("../../vectors/rfc8439/rfc8439.txt");
    let section = text
        .lines()
        .skip_while(|l| *l != "A.3.  Poly1305 Message Authentication Code")
        .skip(1)
        .take_while(|l| !l.starts_with("A.4."));
    let mut vectors = Vec::new();
    // The fields of the current vector, and the one being read.
    let mut fields: [Vec<u8>; 4] = Default::default();
    let mut field = None;
    let mut finish = |fields: &mut [Vec<u8>; 4]| {
        let [key, r_s, msg, tag] = core::mem::take(fields);
        if !tag.is_empty() {
            let key = if key.is_empty() { r_s } else { key };
            vectors.push(Vector { key, msg, tag });
        }
    };
    for line in section {
        let line = line.trim();
        if line.starts_with("Test Vector #") {
            finish(&mut fields);
            field = None;
            continue;
        }
        let label = match line {
            "One-time Poly1305 Key:" => Some(0),
            "R:" | "S:" => Some(1),
            "Text to MAC:" | "data:" => Some(2),
            "Tag:" | "tag:" => Some(3),
            _ => None,
        };
        if label.is_some() {
            field = label;
        } else if let Some(f) = field
            && let Some(row) = dump_row(line).or_else(|| plain_row(line))
        {
            fields[f].extend(row);
        }
    }
    finish(&mut fields);
    vectors
}

#[test]
fn rfc8439_poly1305() {
    let vs = vectors();
    assert_eq!(vs.len(), 11);
    let lens: Vec<usize> = vs.iter().map(|v| v.msg.len()).collect();
    assert_eq!(lens, [64, 375, 375, 127, 16, 16, 48, 48, 16, 64, 48]);
    for v in &vs {
        assert_eq!(v.key.len(), 32);
        let key: [u8; 32] = v.key[..].try_into().unwrap();
        assert_eq!(Poly1305::mac(&key, &v.msg)[..], v.tag[..]);
    }
}

/// Every vector, absorbed in two pieces split at every position, and a byte
/// at a time.
#[test]
fn rfc8439_poly1305_split() {
    for v in &vectors() {
        let key: [u8; 32] = v.key[..].try_into().unwrap();
        for i in 0..=v.msg.len() {
            let mut p = Poly1305::new(&key);
            p.update(&v.msg[..i]);
            p.update(&v.msg[i..]);
            assert_eq!(p.finalize()[..], v.tag[..]);
        }
        let mut p = Poly1305::new(&key);
        for byte in &v.msg {
            p.update(core::slice::from_ref(byte));
        }
        assert_eq!(p.finalize()[..], v.tag[..]);
    }
}
