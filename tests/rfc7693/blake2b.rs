//! BLAKE2b: the example of Appendix A and the self-test of Appendix E.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86"))]

use verified_garbage::hashes::blake2b::{Blake2b, Blake2b512};

use super::{Keyed, c_array, example, selftest};

#[test]
fn blake2b_abc() {
    assert_eq!(
        Blake2b512::digest(b"abc")[..],
        example("BLAKE2b-512(\"abc\")")[..]
    );
}

/// The digest of `data` keyed with `key`, of `outlen` bytes.
fn hash(outlen: usize, key: &[u8], data: &[u8]) -> Vec<u8> {
    let sizes: [(usize, Keyed); 4] = [
        (20, |k, d| Blake2b::<20>::digest_keyed(k, d).to_vec()),
        (32, |k, d| Blake2b::<32>::digest_keyed(k, d).to_vec()),
        (48, |k, d| Blake2b::<48>::digest_keyed(k, d).to_vec()),
        (64, |k, d| Blake2b::<64>::digest_keyed(k, d).to_vec()),
    ];
    let (_, f) = sizes.iter().find(|(n, _)| *n == outlen).unwrap();
    f(key, data)
}

#[test]
fn blake2b_selftest() {
    let md_len = c_array("b2b_md_len");
    assert_eq!(md_len, [20, 32, 48, 64]);
    let result = selftest(&md_len, &c_array("b2b_in_len"), hash, |pieces| {
        let mut h = Blake2b::<32>::new();
        for p in pieces {
            h.update(p);
        }
        h.finalize().to_vec()
    });
    let expected: Vec<u8> = c_array("blake2b_res")
        .into_iter()
        .map(|b| b as u8)
        .collect();
    assert_eq!(expected.len(), 32);
    assert_eq!(result, expected);
}
