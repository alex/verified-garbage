//! TDEA-CMAC: every vector of the CMAC generation and verification files,
//! for two- and three-key TDEA (the MAC truncated to `Tlen` bytes).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::cmac::triple_des::TripleDesCmac;

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
/// `Mac`, with its `Klen` (2 or 3) DES keys: `Key1 ‖ Key2`, or
/// `Key1 ‖ Key2 ‖ Key3`. A two-key vector lists `Key3 = Key1` too (but where
/// it changed `Key1` for a failure), and its MAC with the 24-byte key is the
/// same.
fn matches(v: &[(&str, &str)], keys: usize) -> bool {
    let k: Vec<Vec<u8>> = ["Key1", "Key2", "Key3"]
        .iter()
        .map(|n| unhex(field(v, n)))
        .collect();
    assert_eq!(field(v, "Klen").parse::<usize>().unwrap(), keys);
    // `Mlen` is in bytes; the empty message is written as `Msg = 00`.
    let len: usize = field(v, "Mlen").parse().unwrap();
    let msg = unhex(field(v, "Msg"));
    let tlen: usize = field(v, "Tlen").parse().unwrap();
    let mac = unhex(field(v, "Mac"));
    assert_eq!(mac.len(), tlen);
    let ours = TripleDesCmac::mac(&k[..keys].concat(), &msg[..len]).unwrap();
    if keys == 2 && k[2] == k[0] {
        assert_eq!(TripleDesCmac::mac(&k.concat(), &msg[..len]), Ok(ours));
    }
    ours[..tlen] == mac[..]
}

#[test]
fn generate() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp/cmac-tdes/CMACGenTDES2.rsp"),
            2,
        ),
        (
            include_str!("../../vectors/nist-cavp/cmac-tdes/CMACGenTDES3.rsp"),
            3,
        ),
    ];
    let mut n = 0;
    for (text, keys) in files {
        for v in vectors(text) {
            assert!(matches(&v, keys), "{v:?}");
            n += 1;
        }
    }
    assert_eq!(n, 96 + 96);
}

#[test]
fn verify() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp/cmac-tdes/CMACVerTDES2.rsp"),
            2,
        ),
        (
            include_str!("../../vectors/nist-cavp/cmac-tdes/CMACVerTDES3.rsp"),
            3,
        ),
    ];
    let (mut pass, mut fail) = (0, 0);
    for (text, keys) in files {
        for v in vectors(text) {
            let result = field(&v, "Result");
            if result == "P" {
                assert!(matches(&v, keys), "{v:?}");
                pass += 1;
            } else {
                assert!(result.starts_with("F "), "{v:?}");
                assert!(!matches(&v, keys), "{v:?}");
                fail += 1;
            }
        }
    }
    assert_eq!((pass, fail), (72 + 48, 288 + 192));
}
