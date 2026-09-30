//! BLAKE2s: the example of Appendix B and the self-test of Appendix E.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::hashes::blake2s::{Blake2s, Blake2s256};

use super::{Keyed, c_array, example, selftest};

#[test]
fn blake2s_abc() {
    assert_eq!(
        Blake2s256::digest(b"abc")[..],
        example("BLAKE2s-256(\"abc\")")[..]
    );
}

/// The digest of `data` keyed with `key`, of `outlen` bytes.
fn hash(outlen: usize, key: &[u8], data: &[u8]) -> Vec<u8> {
    let sizes: [(usize, Keyed); 4] = [
        (16, |k, d| Blake2s::<16>::digest_keyed(k, d).to_vec()),
        (20, |k, d| Blake2s::<20>::digest_keyed(k, d).to_vec()),
        (28, |k, d| Blake2s::<28>::digest_keyed(k, d).to_vec()),
        (32, |k, d| Blake2s::<32>::digest_keyed(k, d).to_vec()),
    ];
    let (_, f) = sizes.iter().find(|(n, _)| *n == outlen).unwrap();
    f(key, data)
}

#[test]
fn blake2s_selftest() {
    let md_len = c_array("b2s_md_len");
    assert_eq!(md_len, [16, 20, 28, 32]);
    let result = selftest(&md_len, &c_array("b2s_in_len"), hash, |pieces| {
        let mut h = Blake2s::<32>::new();
        for p in pieces {
            h.update(p);
        }
        h.finalize().to_vec()
    });
    let expected: Vec<u8> = c_array("blake2s_res")
        .into_iter()
        .map(|b| b as u8)
        .collect();
    assert_eq!(expected.len(), 32);
    assert_eq!(result, expected);
}
