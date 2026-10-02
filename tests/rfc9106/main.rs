//! Published RFC 9106 vectors, read from the unmodified RFC, and API boundaries.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use verified_garbage::argon2::{Error, Variant, derive};

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
        for threads in [1, 2, 8] {
            derive(
                variant,
                &input(text, "Password"),
                &input(text, "Salt"),
                number(text, "Passes:"),
                number(text, "Memory:"),
                number(text, "Parallelism:"),
                threads,
                &input(text, "Secret"),
                &input(text, "Associated data"),
                &mut out,
            )
            .unwrap();
            assert_eq!(out, expected, "{variant:?}, threads={threads}");
        }
    }
}

#[test]
fn invalid_parameters_preserve_output() {
    let mut out = [0xa5; 4];
    for (passes, memory, lanes, threads) in [
        (0, 8, 1, 1),
        (1, 8, 0, 1),
        (1, u32::MAX, 1 << 24, 1),
        (1, 8, 1, 0),
        (1, 8, 1, 1 << 24),
        (1, 7, 1, 1),
        (1, 15, 2, 1),
    ] {
        assert_eq!(
            derive(
                Variant::Argon2id,
                b"",
                b"",
                passes,
                memory,
                lanes,
                threads,
                b"",
                b"",
                &mut out
            ),
            Err(Error::InvalidParameters)
        );
        assert_eq!(out, [0xa5; 4]);
    }
    for len in 0..4 {
        assert_eq!(
            derive(
                Variant::Argon2i,
                b"",
                b"",
                1,
                8,
                1,
                1,
                b"",
                b"",
                &mut out[..len]
            ),
            Err(Error::InvalidParameters)
        );
    }
}

#[test]
fn errors() {
    for (error, message) in [
        (Error::InvalidParameters, "invalid Argon2 parameters"),
        (
            Error::AllocationFailed,
            "could not allocate Argon2's memory",
        ),
    ] {
        assert_eq!(error.to_string(), message);
        let _: &dyn std::error::Error = &error;
        assert!(!format!("{error:?}").is_empty());
    }
}
