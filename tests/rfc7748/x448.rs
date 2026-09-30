//! The X448 vectors of RFC 7748 (§5.2 and §6.2), read from the vendored RFC.

#![cfg(target_arch = "x86_64")]

use verified_garbage::x448::{BASE_POINT, PrivateKey, x448};

use super::TEXT;

fn section(from: &str, to: &str) -> &'static str {
    TEXT.split_once(&format!("\n{from}"))
        .unwrap()
        .1
        .split_once(&format!("\n{to}"))
        .unwrap()
        .0
}

/// X448 values occupy two consecutive lines of 56 hex digits.
fn values(text: &str, label: &str) -> Vec<[u8; 56]> {
    let mut lines = text.lines().map(str::trim);
    let mut out = Vec::new();
    while let Some(line) = lines.next() {
        if line == label {
            let hex = format!("{}{}", lines.next().unwrap(), lines.next().unwrap());
            assert_eq!(hex.len(), 112);
            out.push(core::array::from_fn(|i| {
                u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap()
            }));
        }
    }
    out
}

/// §5.2: both scalar-multiplication vectors.
#[test]
fn x448_vectors() {
    let text = section("5.2.  Test Vectors", "   The second type of test vector")
        .split_once("   X448:")
        .unwrap()
        .1;
    let scalars = values(text, "Input scalar:");
    let us = values(text, "Input u-coordinate:");
    let outs = values(text, "Output u-coordinate:");
    assert_eq!((scalars.len(), us.len(), outs.len()), (2, 2, 2));
    for i in 0..2 {
        assert_eq!(x448(&scalars[i], &us[i]), outs[i]);
    }
}

/// §5.2: one and 1,000 iterations from `k = u = 5`.
#[test]
fn iterated() {
    let text = section("   The second type of test vector", "6.  Diffie-Hellman");
    assert_eq!(values(text, "For X448:"), [BASE_POINT]);
    let text = text.split_once("   X448:").unwrap().1;
    let one = values(text, "After one iteration:");
    let thousand = values(text, "After 1,000 iterations:");
    let (mut k, mut u) = (BASE_POINT, BASE_POINT);
    for i in 1..=1000 {
        (k, u) = (x448(&k, &u), k);
        if i == 1 {
            assert_eq!([k], *one);
        }
    }
    assert_eq!([k], *thousand);
}

/// §6.2: the Diffie-Hellman vector.
#[test]
fn diffie_hellman() {
    let text = section("6.2.  Curve448\n", "7.  Security Considerations\n");
    let v = |label| values(text, label)[0];
    let a = PrivateKey::from_bytes(&v("Alice's private key, a:"));
    let b = PrivateKey::from_bytes(&v("Bob's private key, b:"));
    let ka = v("Alice's public key, X448(a, 5):");
    let kb = v("Bob's public key, X448(b, 5):");
    let k = v("Their shared secret, K:");
    assert_eq!(a.public_key(), ka);
    assert_eq!(b.public_key(), kb);
    assert_eq!(a.diffie_hellman(&kb), Ok(k));
    assert_eq!(b.diffie_hellman(&ka), Ok(k));
}

/// A private key does not print its bytes.
#[test]
fn private_key_debug() {
    let a = PrivateKey::from_bytes(&[0x42; 56]);
    assert_eq!(format!("{a:?}"), "PrivateKey { .. }");
}
