//! The X25519 test vectors of RFC 7748 (§5.2 and §6.1).
//!
//! The RFC is vendored under `vectors/rfc7748/` (see
//! `vectors/sources/rfc7748.toml` for where it comes from) and compiled into
//! the test binary, so these tests always run. Each value is the line of 64
//! hex digits after its label; page breaks and prose are skipped.

#![cfg(any(target_arch = "x86_64", target_arch = "arm"))]

use verified_garbage::x25519::{BASE_POINT, PrivateKey, x25519};

const TEXT: &str = include_str!("../../vectors/rfc7748/rfc7748.txt");

/// The values labelled `label` (a line ending with `:`) in the lines from the
/// one starting with `from` to the next one starting with `to`, in order.
fn values(from: &str, to: &str, label: &str) -> Vec<[u8; 32]> {
    let mut lines = TEXT
        .lines()
        .skip_while(|l| !l.starts_with(from))
        .skip(1)
        .take_while(|l| !l.starts_with(to))
        .map(str::trim);
    let mut out = Vec::new();
    while let Some(l) = lines.next() {
        if l == label {
            out.push(hex(lines.next().unwrap()));
        }
    }
    out
}

fn hex(s: &str) -> [u8; 32] {
    assert_eq!(s.len(), 64, "{s}");
    core::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}

/// §5.2: the two X25519 vectors (which come before the X448 ones).
#[test]
fn x25519_vectors() {
    let scalars = values("5.2.  Test Vectors", "   X448:", "Input scalar:");
    let us = values("5.2.  Test Vectors", "   X448:", "Input u-coordinate:");
    let outs = values("5.2.  Test Vectors", "   X448:", "Output u-coordinate:");
    assert_eq!((scalars.len(), us.len(), outs.len()), (2, 2, 2));
    for i in 0..2 {
        assert_eq!(x25519(&scalars[i], &us[i]), outs[i]);
    }
}

/// §5.2: X25519 iterated from `k = u = 9`, `k` becoming the result and `u`
/// the old `k`, after 1 and 1,000 iterations (1,000,000 would take the
/// tests minutes).
#[test]
fn iterated() {
    let from = "   The second type of test vector";
    let one = values(from, "   X448:", "After one iteration:");
    let thousand = values(from, "   X448:", "After 1,000 iterations:");
    assert_eq!(values(from, "   X448:", "For X25519:"), [BASE_POINT]);
    let (mut k, mut u) = (BASE_POINT, BASE_POINT);
    for i in 1..=1000 {
        (k, u) = (x25519(&k, &u), k);
        if i == 1 {
            assert_eq!([k], *one);
        }
    }
    assert_eq!([k], *thousand);
}

/// §6.1: the Diffie-Hellman vector.
#[test]
fn diffie_hellman() {
    let v = |label| values("6.1.  Curve25519", "6.2.  Curve448", label)[0];
    let a = PrivateKey::from_bytes(&v("Alice's private key, a:"));
    let b = PrivateKey::from_bytes(&v("Bob's private key, b:"));
    let ka = v("Alice's public key, X25519(a, 9):");
    let kb = v("Bob's public key, X25519(b, 9):");
    let k = v("Their shared secret, K:");
    assert_eq!(a.public_key(), ka);
    assert_eq!(b.public_key(), kb);
    assert_eq!(a.diffie_hellman(&kb), Ok(k));
    assert_eq!(b.diffie_hellman(&ka), Ok(k));
}

/// A private key does not print its bytes.
#[test]
fn private_key_debug() {
    let a = PrivateKey::from_bytes(&[0x42; 32]);
    assert_eq!(format!("{a:?}"), "PrivateKey { .. }");
}
