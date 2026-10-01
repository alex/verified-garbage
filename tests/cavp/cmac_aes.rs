//! AES-CMAC: every vector of the CMAC generation and verification files,
//! for 128-, 192- and 256-bit keys (the MAC truncated to `Tlen` bytes).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::cmac::aes::AesCmac;

use super::{fields, unhex};

/// The vectors of a CMAC response file: the fields of each, from its
/// `Count` line to the next one.
fn vectors(text: &str) -> Vec<Vec<(&str, &str)>> {
    let mut vs: Vec<Vec<(&str, &str)>> = Vec::new();
    for (k, v) in fields(text) {
        if k == "Count" {
            vs.push(Vec::new());
        }
        vs.last_mut().unwrap().push((k, v));
    }
    vs
}

/// The value of the field `key` of a vector.
fn field<'a>(v: &[(&str, &'a str)], key: &str) -> &'a str {
    v.iter().find(|(k, _)| *k == key).unwrap().1
}

/// Whether the MAC of a vector's message (truncated to its `Tlen`) is its
/// `Mac`; its key must be `bytes` long.
fn matches(v: &[(&str, &str)], bytes: usize) -> bool {
    let key = unhex(field(v, "Key"));
    assert_eq!(key.len(), bytes);
    assert_eq!(field(v, "Klen").parse::<usize>().unwrap(), bytes);
    // `Mlen` is in bytes; the empty message is written as `Msg = 00`.
    let len: usize = field(v, "Mlen").parse().unwrap();
    let msg = unhex(field(v, "Msg"));
    let tlen: usize = field(v, "Tlen").parse().unwrap();
    let mac = unhex(field(v, "Mac"));
    assert_eq!(mac.len(), tlen);
    AesCmac::mac(&key, &msg[..len]).unwrap()[..tlen] == mac[..]
}

#[test]
fn generate() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp/cmac-aes/CMACGenAES128.rsp"),
            16,
        ),
        (
            include_str!("../../vectors/nist-cavp/cmac-aes/CMACGenAES192.rsp"),
            24,
        ),
        (
            include_str!("../../vectors/nist-cavp/cmac-aes/CMACGenAES256.rsp"),
            32,
        ),
    ];
    let mut n = 0;
    for (text, bytes) in files {
        for v in vectors(text) {
            assert!(matches(&v, bytes), "{v:?}");
            n += 1;
        }
    }
    assert_eq!(n, 96 + 144 + 96);
}

#[test]
fn verify() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp/cmac-aes/CMACVerAES128.rsp"),
            16,
        ),
        (
            include_str!("../../vectors/nist-cavp/cmac-aes/CMACVerAES256.rsp"),
            32,
        ),
    ];
    let (mut pass, mut fail) = (0, 0);
    for (text, bytes) in files {
        for v in vectors(text) {
            let result = field(&v, "Result");
            if result == "P" {
                assert!(matches(&v, bytes), "{v:?}");
                pass += 1;
            } else {
                assert!(result.starts_with("F "), "{v:?}");
                assert!(!matches(&v, bytes), "{v:?}");
                fail += 1;
            }
        }
    }
    assert_eq!((pass, fail), (48 + 48, 192 + 192));
}
