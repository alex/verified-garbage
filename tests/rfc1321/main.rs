//! The MD5 test suite of RFC 1321 (Appendix A.5).
//!
//! The RFC is vendored under `vectors/rfc1321/` (see `vectors/sources.toml`
//! for where it comes from) and compiled into the test binary, so these tests
//! always run. Every vector of the suite is checked, in one call and split
//! into pieces at every position.

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::HashFunction;
use verified_garbage::hashes::md5::Md5;

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// The `(message, digest)` of each `MD5 ("message") = digest` line of the
/// test suite. The RFC wraps two of them onto a second line, so the suite's
/// lines are joined without separators before they are split into vectors.
fn vectors() -> Vec<(Vec<u8>, Vec<u8>)> {
    let text = include_str!("../../vectors/rfc1321/rfc1321.txt");
    let suite: String = text
        .lines()
        .skip_while(|l| *l != "MD5 test suite:")
        .skip(1)
        .take_while(|l| !l.is_empty())
        .collect();
    let mut pieces = suite.split("MD5 (\"");
    assert_eq!(pieces.next(), Some(""));
    pieces
        .map(|v| {
            let (msg, md) = v.split_once("\") =").unwrap();
            (msg.as_bytes().to_vec(), unhex(md.trim()))
        })
        .collect()
}

#[test]
fn rfc1321_test_suite() {
    let vs = vectors();
    assert_eq!(vs.len(), 7);
    for (msg, md) in &vs {
        assert_eq!(Md5::digest(msg)[..], md[..]);
        assert_eq!(<Md5 as HashFunction>::digest(msg)[..], md[..]);
    }
}

/// Every vector, absorbed in two pieces split at every position, and in
/// three pieces split at every pair of positions.
#[test]
fn rfc1321_test_suite_split() {
    for (msg, md) in &vectors() {
        for i in 0..=msg.len() {
            let mut h = Md5::new();
            h.update(&msg[..i]);
            h.update(&msg[i..]);
            assert_eq!(h.finalize()[..], md[..]);
            for j in i..=msg.len() {
                let mut h = Md5::default();
                h.update(&msg[..i]);
                h.update(&msg[i..j]);
                h.update(&msg[j..]);
                assert_eq!(h.finalize()[..], md[..]);
            }
        }
    }
}
