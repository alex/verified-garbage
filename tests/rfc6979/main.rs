//! Deterministic ECDSA known-answer tests from the vendored RFC 6979,
//! §A.2.5 (P-256): the private key, and its signatures of "sample" and
//! "test" with SHA-256.

#![cfg(target_arch = "x86_64")]

use verified_garbage::ecdsa::{Error, P256, SigningKey};
use verified_garbage::hashes::sha256::Sha256;

const TEXT: &str = include_str!("../../vectors/rfc6979/rfc6979.txt");

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0, "{s}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// The hex value of the first line from `lines` that begins with `label`.
fn value<'a>(lines: &mut impl Iterator<Item = &'a str>, label: &str) -> [u8; 32] {
    let line = lines.find(|l| l.starts_with(label)).unwrap();
    unhex(&line[label.len()..]).try_into().unwrap()
}

/// Each message, with the `r ‖ s` of its SHA-256 signature.
type Signatures = Vec<(String, [u8; 64])>;

/// `q`, `x`, and the SHA-256 signatures.
fn p256() -> ([u8; 32], [u8; 32], Signatures) {
    let text = TEXT
        .split_once("\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n")
        .unwrap()
        .1;
    let text = text.split_once("\nA.").unwrap().0;
    let mut lines = text.lines().map(str::trim);
    let q = value(&mut lines, "q = ");
    let x = value(&mut lines, "x = ");
    let mut signatures = Vec::new();
    while let Some(line) = lines.next() {
        let Some(message) = line.strip_prefix("With SHA-256, message = \"") else {
            continue;
        };
        let message = message.strip_suffix("\":").unwrap();
        let mut rs = [0; 64];
        rs[..32].copy_from_slice(&value(&mut lines, "r = "));
        rs[32..].copy_from_slice(&value(&mut lines, "s = "));
        signatures.push((message.to_string(), rs));
    }
    assert_eq!(signatures.len(), 2);
    (q, x, signatures)
}

/// The integer `x + delta` (mod 2²⁵⁶) of the 32 bytes `x`.
fn add(x: &[u8; 32], delta: i16) -> [u8; 32] {
    let mut out = *x;
    let mut carry = delta;
    for b in out.iter_mut().rev() {
        let v = i16::from(*b) + carry;
        *b = v.rem_euclid(256) as u8;
        carry = v.div_euclid(256);
    }
    out
}

#[test]
fn p256_sha256() {
    let (_, x, signatures) = p256();
    let key = SigningKey::<P256>::from_bytes(&x);
    for (message, rs) in &signatures {
        assert_eq!(key.sign_sha256(message.as_bytes()), Ok(*rs), "{message}");
        let prehashed = key
            .clone()
            .sign_sha256_prehashed(&Sha256::digest(message.as_bytes()));
        assert_eq!(prehashed, Ok(*rs), "{message}");
    }
    assert_eq!(format!("{key:?}"), "SigningKey { .. }");
}

/// A key outside `[1, n − 1]` is refused; those at its ends sign.
#[test]
fn p256_keys() {
    let (q, _, _) = p256();
    for bad in [[0; 32], q, add(&q, 1), [0xff; 32]] {
        let key = SigningKey::<P256>::from_bytes(&bad);
        assert_eq!(key.sign_sha256(b"sample"), Err(Error::InvalidKey));
    }
    for good in [add(&[0; 32], 1), add(&q, -1)] {
        assert!(
            SigningKey::<P256>::from_bytes(&good)
                .sign_sha256(b"sample")
                .is_ok()
        );
    }
    assert_eq!(Error::InvalidKey.to_string(), "invalid ECDSA private key");
}
