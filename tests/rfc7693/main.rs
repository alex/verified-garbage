//! The BLAKE2 examples and self-test of RFC 7693: the digests of `"abc"`
//! (Appendices A and B) and the self-test module (Appendix E), which hashes
//! generated data of several lengths, unkeyed and keyed, for several digest
//! sizes, and checks a hash of all the digests.
//!
//! The RFC is vendored under `vectors/rfc7693/` (see
//! `vectors/sources/rfc7693.toml` for where it comes from) and compiled into
//! the test binary, so these tests always run. The expected values and the
//! self-test's parameter sets are read from the RFC's text; the self-test's
//! data generator, `selftest_seq`, is transcribed from its C source.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

mod blake2b;
mod blake2s;

/// A keyed hash function of one digest size: `(key, data)` to the digest.
type Keyed = fn(&[u8], &[u8]) -> Vec<u8>;

const TEXT: &str = include_str!("../../vectors/rfc7693/rfc7693.txt");

/// The digest `label = ...` of an example: the hex bytes after it, up to the
/// next blank line.
fn example(label: &str) -> Vec<u8> {
    let start = TEXT.find(label).unwrap() + label.len();
    let rest = TEXT[start..].trim_start().strip_prefix('=').unwrap();
    rest.lines()
        .take_while(|l| !l.trim().is_empty())
        .flat_map(str::split_whitespace)
        .map(|b| u8::from_str_radix(b, 16).unwrap())
        .collect()
}

/// The elements of the C array `name` in Appendix E (`name[n] = { ... };`),
/// decimal or `0x` hex.
fn c_array(name: &str) -> Vec<usize> {
    let start = TEXT.find(&format!(" {name}[")).unwrap();
    let body = &TEXT[start..];
    let body = &body[body.find('{').unwrap() + 1..body.find("};").unwrap()];
    body.split(',')
        .map(str::trim)
        .map(|x| match x.strip_prefix("0x") {
            Some(h) => usize::from_str_radix(h, 16).unwrap(),
            None => x.parse().unwrap(),
        })
        .collect()
}

/// `selftest_seq` (Appendix E): `len` bytes of a Fibonacci generator seeded
/// with `seed`.
fn selftest_seq(len: usize, seed: u32) -> Vec<u8> {
    let mut a = 0xDEAD4BADu32.wrapping_mul(seed);
    let mut b = 1u32;
    (0..len)
        .map(|_| {
            let t = a.wrapping_add(b);
            a = b;
            b = t;
            (t >> 24) as u8
        })
        .collect()
}

/// The self-test of Appendix E for a function whose digests of each size in
/// `md_len` are computed by `hash(outlen, key, data)`, and whose 32-byte
/// digest is computed incrementally by `grand` from the pieces it is given:
/// the digest of all the digests.
fn selftest(
    md_len: &[usize],
    in_len: &[usize],
    hash: impl Fn(usize, &[u8], &[u8]) -> Vec<u8>,
    grand: impl Fn(&[Vec<u8>]) -> Vec<u8>,
) -> Vec<u8> {
    let mut digests = Vec::new();
    for &outlen in md_len {
        for &inlen in in_len {
            let data = selftest_seq(inlen, inlen as u32);
            digests.push(hash(outlen, &[], &data));
            let key = selftest_seq(outlen, outlen as u32);
            digests.push(hash(outlen, &key, &data));
        }
    }
    grand(&digests)
}
