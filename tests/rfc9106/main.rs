//! Published RFC 9106 vectors, read from the unmodified RFC, and API boundaries.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use verified_garbage::argon2::{
    Error, Params, Variant, derive, derive_keyed, verify, verify_keyed,
};

fn bytes(text: &str, label: &str, length: usize) -> Vec<u8> {
    text.split_once(label)
        .unwrap()
        .1
        .split_whitespace()
        .take(length)
        .map(|s| u8::from_str_radix(s, 16).unwrap())
        .collect()
}

fn number(text: &str, label: &str) -> u32 {
    text.split_once(label)
        .unwrap()
        .1
        .split_whitespace()
        .next()
        .unwrap()
        .trim_end_matches(',')
        .parse()
        .unwrap()
}

fn input(text: &str, label: &str) -> Vec<u8> {
    let rest = text.split_once(&format!("{label}[")).unwrap().1;
    let (length, data) = rest.split_once("]:").unwrap();
    data.split_whitespace()
        .take(length.parse().unwrap())
        .map(|s| u8::from_str_radix(s, 16).unwrap())
        .collect()
}

fn params(variant: Variant, iterations: u32, memory_kib: u32, lanes: u32) -> Params {
    Params {
        variant,
        iterations,
        memory_kib,
        lanes,
    }
}

#[test]
fn rfc9106_vectors() {
    let text = include_str!("../../vectors/rfc9106/rfc9106.txt");
    for (variant, name) in [
        (Variant::Argon2d, "Argon2d"),
        (Variant::Argon2i, "Argon2i"),
        (Variant::Argon2id, "Argon2id"),
    ] {
        let text = text
            .split_once(&format!("{name} version number 19"))
            .unwrap()
            .1;
        let expected = bytes(text, "Tag:", number(text, "Tag length:") as usize);
        let mut out = vec![0; expected.len()];
        derive_keyed(
            &Params {
                variant,
                iterations: number(text, "Passes:"),
                memory_kib: number(text, "Memory:"),
                lanes: number(text, "Parallelism:"),
            },
            &input(text, "Password"),
            &input(text, "Salt"),
            &input(text, "Secret"),
            &input(text, "Associated data"),
            usize::MAX,
            &mut out,
        )
        .unwrap();
        assert_eq!(out, expected, "{variant:?}");
    }
}

#[test]
fn derive_is_unkeyed() {
    for variant in [Variant::Argon2d, Variant::Argon2i, Variant::Argon2id] {
        let p = params(variant, 2, 32, 2);
        let mut expected = [0; 32];
        derive_keyed(
            &p,
            b"password",
            b"saltsalt",
            b"",
            b"",
            32 << 10,
            &mut expected,
        )
        .unwrap();
        let mut out = [0; 32];
        derive(&p, b"password", b"saltsalt", 32 << 10, &mut out).unwrap();
        assert_eq!(out, expected, "{variant:?}");
    }
}

#[test]
fn invalid_parameters_preserve_output() {
    let mut out = [0xa5; 4];
    for (passes, memory, lanes) in [
        (0, 8, 1),
        (1, 8, 0),
        (1, u32::MAX, 1 << 24),
        (1, 7, 1),
        (1, 15, 2),
    ] {
        let p = params(Variant::Argon2id, passes, memory, lanes);
        assert_eq!(
            derive(&p, b"", b"", usize::MAX, &mut out),
            Err(Error::InvalidParameters)
        );
        assert_eq!(out, [0xa5; 4]);
    }
    for len in 0..4 {
        assert_eq!(
            derive(
                &params(Variant::Argon2i, 1, 8, 1),
                b"",
                b"",
                usize::MAX,
                &mut out[..len]
            ),
            Err(Error::InvalidParameters)
        );
    }
}

#[test]
fn memory_limit() {
    // The matrix has `memory_kib` rounded down to a multiple of `4 · lanes`
    // blocks of 1024 bytes; the 16 KiB of working space are not counted.
    for (memory, lanes, blocks) in [(8, 1, 8), (11, 1, 8), (23, 2, 16)] {
        let p = params(Variant::Argon2id, 1, memory, lanes);
        let mut out = [0xa5; 4];
        assert_eq!(
            derive(&p, b"", b"", blocks * 1024 - 1, &mut out),
            Err(Error::MemoryLimitExceeded)
        );
        assert_eq!(out, [0xa5; 4]);
        derive(&p, b"", b"", blocks * 1024, &mut out).unwrap();
        assert_ne!(out, [0xa5; 4]);
    }
    // The largest matrix, almost 4 TiB, is refused before it is allocated.
    let mut out = [0xa5; 4];
    let largest = params(Variant::Argon2id, 1, u32::MAX, 1);
    let bytes = (u32::MAX as usize & !3) * 1024;
    assert_eq!(
        derive(&largest, b"", b"", bytes - 1, &mut out),
        Err(Error::MemoryLimitExceeded)
    );
    assert_eq!(out, [0xa5; 4]);
}

#[test]
fn errors() {
    for (error, message) in [
        (Error::InvalidParameters, "invalid Argon2 parameters"),
        (
            Error::MemoryLimitExceeded,
            "Argon2 would need more than the memory limit",
        ),
        (
            Error::AllocationFailed,
            "could not allocate Argon2's memory",
        ),
        (Error::KeyMismatch, "Argon2 derived key does not match"),
    ] {
        assert_eq!(error.to_string(), message);
        let _: &dyn std::error::Error = &error;
        assert!(!format!("{error:?}").is_empty());
    }
}

/// `check` accepts `key` and rejects it with a bit flipped in its first, a
/// middle or its last byte.
fn check_verify<const N: usize>(key: &[u8; N], check: impl Fn(&[u8; N]) -> Result<(), Error>) {
    assert_eq!(check(key), Ok(()));
    for i in [0, N / 2, N - 1] {
        let mut bad = *key;
        bad[i] ^= 1;
        assert_eq!(check(&bad), Err(Error::KeyMismatch));
    }
}

/// `verify_keyed` accepts the RFC's tags and rejects any other, or a
/// password other than the RFC's.
#[test]
fn rfc9106_verify_keyed() {
    let text = include_str!("../../vectors/rfc9106/rfc9106.txt");
    for (variant, name) in [
        (Variant::Argon2d, "Argon2d"),
        (Variant::Argon2i, "Argon2i"),
        (Variant::Argon2id, "Argon2id"),
    ] {
        let text = text
            .split_once(&format!("{name} version number 19"))
            .unwrap()
            .1;
        let expected = bytes(text, "Tag:", number(text, "Tag length:") as usize);
        let expected: [u8; 32] = expected.try_into().unwrap();
        let p = Params {
            variant,
            iterations: number(text, "Passes:"),
            memory_kib: number(text, "Memory:"),
            lanes: number(text, "Parallelism:"),
        };
        let (salt, secret, ad) = (
            input(text, "Salt"),
            input(text, "Secret"),
            input(text, "Associated data"),
        );
        let password = input(text, "Password");
        check_verify(&expected, |e| {
            verify_keyed(&p, &password, &salt, &secret, &ad, usize::MAX, e)
        });
        let mut other = password.clone();
        other[0] ^= 1;
        assert_eq!(
            verify_keyed(&p, &other, &salt, &secret, &ad, usize::MAX, &expected),
            Err(Error::KeyMismatch)
        );
    }
}

/// `verify` checks the unkeyed key `derive` derives, and only at the length
/// it was derived with: Argon2's keys of different lengths share no prefix,
/// so neither a prefix of it nor it with a byte appended verifies.
#[test]
fn verify_is_unkeyed() {
    for variant in [Variant::Argon2d, Variant::Argon2i, Variant::Argon2id] {
        let p = params(variant, 2, 32, 2);
        let mut key = [0; 32];
        derive(&p, b"password", b"saltsalt", 32 << 10, &mut key).unwrap();
        check_verify(&key, |e| verify(&p, b"password", b"saltsalt", 32 << 10, e));
        assert_eq!(
            verify(&p, b"passwore", b"saltsalt", 32 << 10, &key),
            Err(Error::KeyMismatch)
        );
        let prefix: [u8; 16] = key[..16].try_into().unwrap();
        assert_eq!(
            verify(&p, b"password", b"saltsalt", 32 << 10, &prefix),
            Err(Error::KeyMismatch)
        );
        let mut longer = [0; 33];
        longer[..32].copy_from_slice(&key);
        assert_eq!(
            verify(&p, b"password", b"saltsalt", 32 << 10, &longer),
            Err(Error::KeyMismatch)
        );
    }
}

/// `verify` and `verify_keyed` refuse what `derive_keyed` refuses: invalid
/// parameters and more memory than the limit.
#[test]
fn verify_errors() {
    let p = params(Variant::Argon2id, 1, 8, 1);
    let mut key = [0; 16];
    derive(&p, b"", b"", 8 << 10, &mut key).unwrap();
    assert_eq!(
        verify(&params(Variant::Argon2id, 0, 8, 1), b"", b"", 8 << 10, &key),
        Err(Error::InvalidParameters)
    );
    assert_eq!(
        verify_keyed(
            &params(Variant::Argon2id, 1, 7, 1),
            b"",
            b"",
            b"",
            b"",
            8 << 10,
            &key
        ),
        Err(Error::InvalidParameters)
    );
    assert_eq!(
        verify(&p, b"", b"", (8 << 10) - 1, &key),
        Err(Error::MemoryLimitExceeded)
    );
    assert_eq!(verify(&p, b"", b"", 8 << 10, &key), Ok(()));
}
