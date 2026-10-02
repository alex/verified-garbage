//! The scrypt test vectors of RFC 7914 (§12), and scrypt's parameter checks.
//!
//! The RFC is vendored under `vectors/rfc7914/` (see
//! `vectors/sources/rfc7914.toml` for where it comes from) and compiled into
//! the test binary, so these tests always run.

#![cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86"
    ),
    feature = "alloc"
))]

use verified_garbage::scrypt::{Error, scrypt, verify};

/// One `scrypt (P="…", S="…", N=…, r=…, p=…, dkLen=…) = <hex>` vector.
struct Vector {
    password: Vec<u8>,
    salt: Vec<u8>,
    n: u64,
    r: u32,
    p: u32,
    dk: Vec<u8>,
}

fn unhex(s: &str) -> Vec<u8> {
    let s: String = s.split_whitespace().collect();
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// The value of `name=` in `params`, up to the next `,` or `)`.
fn param<'a>(params: &'a str, name: &str) -> &'a str {
    let rest = params.split_once(&format!("{name}=")).unwrap().1;
    rest.split([',', ')']).next().unwrap()
}

/// The vectors of §12: each starts at a `scrypt (` line and ends at the next
/// blank line.
fn vectors() -> Vec<Vector> {
    let text = include_str!("../../vectors/rfc7914/rfc7914.txt");
    let section = text
        .split_once("12.  Test Vectors for scrypt")
        .unwrap()
        .1
        .split_once("13.  ")
        .unwrap()
        .0;
    section
        .split("scrypt (")
        .skip(1)
        .map(|v| {
            let v = v.split("\n\n").next().unwrap();
            let (params, dk) = v.split_once(") =").unwrap();
            let unquote = |s: &str| s.trim_matches('"').as_bytes().to_vec();
            Vector {
                password: unquote(param(params, "P")),
                salt: unquote(param(params, "S")),
                n: param(params, "N").parse().unwrap(),
                r: param(params, "r").parse().unwrap(),
                p: param(params, "p").parse().unwrap(),
                dk: unhex(dk),
            }
        })
        .collect()
}

fn check(v: &Vector) {
    let mut dk = vec![0u8; v.dk.len()];
    scrypt(&v.password, &v.salt, v.n, v.r, v.p, usize::MAX, &mut dk).unwrap();
    assert_eq!(dk, v.dk, "N={} r={} p={}", v.n, v.r, v.p);
}

/// Every vector (the last one needs 1 GiB).
#[test]
fn rfc7914_vectors() {
    let vs = vectors();
    assert_eq!(vs.len(), 4);
    for v in &vs {
        check(v);
    }
}

/// A key shorter or longer than the RFC's is a prefix of, or extends, its key
/// (PBKDF2's output blocks do not depend on its length).
#[test]
fn key_lengths() {
    let v = &vectors()[0];
    for len in [1, 32, 33, 64, 100] {
        let mut dk = vec![0u8; len];
        scrypt(&v.password, &v.salt, v.n, v.r, v.p, usize::MAX, &mut dk).unwrap();
        assert_eq!(dk[..len.min(64)], v.dk[..len.min(64)]);
    }
}

/// The memory limit is exactly `128 (r (n + p) + r + 2)` bytes.
#[test]
fn memory_limit() {
    let mut dk = [0u8; 64];
    let need = 128 * (8 * (16 + 2) + 8 + 2);
    assert_eq!(scrypt(b"pw", b"salt", 16, 8, 2, need, &mut dk), Ok(()));
    assert_eq!(
        scrypt(b"pw", b"salt", 16, 8, 2, need - 1, &mut dk),
        Err(Error::MemoryLimitExceeded)
    );
    // More than the address space.
    assert_eq!(
        scrypt(b"pw", b"salt", 1 << 62, 4, 1, usize::MAX, &mut dk),
        Err(Error::MemoryLimitExceeded)
    );
    assert_eq!(
        scrypt(b"pw", b"salt", 1 << 57, 4, 1, usize::MAX, &mut dk),
        Err(Error::MemoryLimitExceeded)
    );
}

/// An allocation of 2⁶² bytes (on 64-bit targets) or 2³¹ bytes (more than
/// `isize::MAX`, on 32-bit targets) fails.
#[test]
fn allocation_failure() {
    let mut dk = [0u8; 64];
    #[cfg(target_pointer_width = "64")]
    let n = 1 << 53;
    #[cfg(target_pointer_width = "32")]
    let n = 1 << 22;
    assert_eq!(
        scrypt(b"pw", b"salt", n, 4, 1, usize::MAX, &mut dk),
        Err(Error::AllocationFailed)
    );
}

#[test]
fn invalid_parameters() {
    let mut dk = [0u8; 64];
    let bad = |n: u64, r: u32, p: u32, dk: &mut [u8]| {
        let got = scrypt(b"pw", b"salt", n, r, p, usize::MAX, dk);
        assert_eq!(got, Err(Error::InvalidParameters));
    };
    // `n` a power of two greater than 1.
    bad(0, 1, 1, &mut dk);
    bad(1, 1, 1, &mut dk);
    bad(3, 1, 1, &mut dk);
    bad(1000, 1, 1, &mut dk);
    // `n < 2^(16 r)`.
    bad(1 << 16, 1, 1, &mut dk);
    bad(1 << 32, 2, 1, &mut dk);
    bad(1 << 48, 3, 1, &mut dk);
    // `r` and `p` positive, `p ≤ (2³² − 1) · 32 / (128 r)`.
    bad(16, 0, 1, &mut dk);
    bad(16, 1, 0, &mut dk);
    bad(16, 1, 1 << 30, &mut dk);
    bad(16, 8, (1 << 27) - 1 + 1, &mut dk);
    // The derived key's length.
    bad(16, 1, 1, &mut []);
    assert_eq!(
        Error::InvalidParameters.to_string(),
        "invalid scrypt parameters"
    );
    assert_eq!(
        Error::MemoryLimitExceeded.to_string(),
        "scrypt would need more than the memory limit"
    );
    assert_eq!(
        Error::AllocationFailed.to_string(),
        "could not allocate scrypt's memory"
    );
    assert_eq!(
        Error::KeyMismatch.to_string(),
        "scrypt derived key does not match"
    );
}

/// `verify` accepts the RFC's keys, and a key derived with a length of its
/// own (each is a prefix of the longer ones), and rejects any other: with a
/// bit flipped in its first, a middle or its last byte, with a byte
/// appended that is not the next one derived, and from another password.
#[test]
fn verify_keys() {
    let vs = vectors();
    for v in &vs[..2] {
        let check =
            |expected: &[u8]| verify(&v.password, &v.salt, v.n, v.r, v.p, usize::MAX, expected);
        assert_eq!(check(&v.dk), Ok(()));
        for i in [0, 32, 63] {
            let mut bad = v.dk.clone();
            bad[i] ^= 1;
            assert_eq!(check(&bad), Err(Error::KeyMismatch));
        }
        assert_eq!(check(&v.dk[..1]), Ok(()));
        assert_eq!(check(&v.dk[..63]), Ok(()));
        let mut longer = vec![0u8; 65];
        scrypt(&v.password, &v.salt, v.n, v.r, v.p, usize::MAX, &mut longer).unwrap();
        assert_eq!(longer[..64], v.dk[..]);
        assert_eq!(check(&longer), Ok(()));
        longer[64] ^= 1;
        assert_eq!(check(&longer), Err(Error::KeyMismatch));
        let other = verify(b"passwore", &v.salt, v.n, v.r, v.p, usize::MAX, &v.dk);
        assert_eq!(other, Err(Error::KeyMismatch));
    }
}

/// `verify` refuses what `scrypt` refuses: an empty key, invalid
/// parameters and more memory than the limit.
#[test]
fn verify_errors() {
    let v = &vectors()[0];
    let need = 128 * (v.r as usize * (v.n as usize + v.p as usize) + v.r as usize + 2);
    let check = |n, max_memory, expected: &[u8]| {
        verify(&v.password, &v.salt, n, v.r, v.p, max_memory, expected)
    };
    assert_eq!(check(v.n, need, &[]), Err(Error::InvalidParameters));
    assert_eq!(check(3, need, &v.dk), Err(Error::InvalidParameters));
    assert_eq!(check(v.n, need - 1, &v.dk), Err(Error::MemoryLimitExceeded));
    assert_eq!(check(v.n, need, &v.dk), Ok(()));
}

/// The largest `n` for `r = 1` and the largest `p` are accepted (and then
/// stopped by the memory limit, before any work).
#[test]
fn largest_parameters() {
    let mut dk = [0u8; 64];
    assert_eq!(
        scrypt(b"pw", b"salt", 1 << 15, 1, 1, 0, &mut dk),
        Err(Error::MemoryLimitExceeded)
    );
    assert_eq!(
        scrypt(b"pw", b"salt", 16, 1, (1 << 30) - 1, 0, &mut dk),
        Err(Error::MemoryLimitExceeded)
    );
    assert_eq!(
        scrypt(b"pw", b"salt", 1 << 63, 4, 1, 0, &mut dk),
        Err(Error::MemoryLimitExceeded)
    );
}
