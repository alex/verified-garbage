//! SHA3-224, SHA3-256, SHA3-384 and SHA3-512: for each, every message length
//! from 0 to the rate in bytes, the long messages, and the Monte Carlo test.
//! SHAKE128 and SHAKE256: the short and long messages, the variable output
//! lengths, and the Monte Carlo test.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use super::{fields, unhex};

/// Checks every `Len`/`Msg`/`MD` vector of a message test file for a
/// hash function `digest` with `N`-byte digests (whose header gives the
/// digest length in bits), and returns how many there were.
fn check_messages<const N: usize>(text: &str, digest: fn(&[u8]) -> [u8; N]) -> usize {
    assert!(text.contains(&format!("[L = {}]", 8 * N)));
    let fields = fields(text);
    assert_eq!(fields.len() % 3, 0);
    for v in fields.chunks(3) {
        assert_eq!([v[0].0, v[1].0, v[2].0], ["Len", "Msg", "MD"]);
        let len: usize = v[0].1.parse().unwrap();
        assert_eq!(len % 8, 0);
        let msg = unhex(v[1].1);
        assert_eq!(digest(&msg[..len / 8])[..], unhex(v[2].1));
    }
    fields.len() / 3
}
use verified_garbage::hashes::sha3::{Sha3_224, Sha3_256, Sha3_384, Sha3_512, Shake128, Shake256};

/// The SHA3VS Monte Carlo test of a hash function `digest` with `N`-byte
/// digests: 100 checkpoints, each after 1000 iterations of hashing the
/// previous digest.
fn check_monte_carlo<const N: usize>(text: &str, digest: fn(&[u8]) -> [u8; N]) {
    assert!(text.contains(&format!("[L = {}]", 8 * N)));
    let fields = fields(text);
    assert_eq!(fields[0].0, "Seed");
    let mut md: [u8; N] = unhex(fields[0].1).try_into().unwrap();
    let checkpoints = &fields[1..];
    assert_eq!(checkpoints.len(), 2 * 100);
    for (j, v) in checkpoints.chunks(2).enumerate() {
        assert_eq!([v[0].0, v[1].0], ["COUNT", "MD"]);
        assert_eq!(v[0].1, j.to_string());
        for _ in 0..1000 {
            md = digest(&md);
        }
        assert_eq!(md[..], unhex(v[1].1));
    }
}

macro_rules! cavp {
    ($name:ident, $hash:ident, $file:literal, $short:literal, $long:literal) => {
        mod $name {
            use super::*;

            #[test]
            fn short_messages() {
                let n = check_messages(
                    include_str!(concat!(
                        "../../vectors/nist-cavp/sha3/",
                        $file,
                        "ShortMsg.rsp"
                    )),
                    $hash::digest,
                );
                assert_eq!(n, $short);
            }

            #[test]
            fn long_messages() {
                let n = check_messages(
                    include_str!(concat!(
                        "../../vectors/nist-cavp/sha3/",
                        $file,
                        "LongMsg.rsp"
                    )),
                    $hash::digest,
                );
                assert_eq!(n, $long);
            }

            #[test]
            fn monte_carlo() {
                check_monte_carlo(
                    include_str!(concat!("../../vectors/nist-cavp/sha3/", $file, "Monte.rsp")),
                    $hash::digest,
                );
            }
        }
    };
}

cavp!(sha3_224, Sha3_224, "SHA3_224", 145, 100);
cavp!(sha3_256, Sha3_256, "SHA3_256", 137, 100);
cavp!(sha3_384, Sha3_384, "SHA3_384", 105, 100);
cavp!(sha3_512, Sha3_512, "SHA3_512", 73, 100);

/// Checks every `Len`/`Msg`/`Output` vector of a SHAKE message test file,
/// whose outputs are `out` bytes, and returns how many there were.
fn check_shake_messages(text: &str, out: usize, xof: fn(&[u8], &mut [u8])) -> usize {
    assert!(text.contains(&format!("[Outputlen = {}]", 8 * out)));
    let fields = fields(text);
    assert_eq!(fields.len() % 3, 0);
    for v in fields.chunks(3) {
        assert_eq!([v[0].0, v[1].0, v[2].0], ["Len", "Msg", "Output"]);
        let len: usize = v[0].1.parse().unwrap();
        assert_eq!(len % 8, 0);
        let msg = unhex(v[1].1);
        let mut output = vec![0; out];
        xof(&msg[..len / 8], &mut output);
        assert_eq!(output, unhex(v[2].1));
    }
    fields.len() / 3
}

/// Checks every vector of a SHAKE `VariableOut` file, and returns how
/// many there were.
fn check_shake_variable(text: &str, xof: fn(&[u8], &mut [u8])) -> usize {
    let fields = fields(text);
    assert_eq!(fields.len() % 4, 0);
    for v in fields.chunks(4) {
        assert_eq!(
            [v[0].0, v[1].0, v[2].0, v[3].0],
            ["COUNT", "Outputlen", "Msg", "Output"]
        );
        let bits: usize = v[1].1.parse().unwrap();
        assert_eq!(bits % 8, 0);
        let mut output = vec![0; bits / 8];
        xof(&unhex(v[2].1), &mut output);
        assert_eq!(output, unhex(v[3].1));
    }
    fields.len() / 4
}

/// The SHAKE Monte Carlo test (SHA3VS §6.3.3): 100 checkpoints of 1000
/// iterations, each hashing the leftmost 16 bytes of the previous
/// output to an output whose length is derived from its last 2 bytes.
/// Output lengths are from `min` to `max` bytes; a shorter output is
/// padded with zeros to 16 bytes.
fn check_shake_monte_carlo(text: &str, min: usize, max: usize, xof: fn(&[u8], &mut [u8])) {
    assert!(text.contains(&format!("[Minimum Output Length (bits) = {}]", 8 * min)));
    assert!(text.contains(&format!("[Maximum Output Length (bits) = {}]", 8 * max)));
    let fields = fields(text);
    assert_eq!(fields[0].0, "Msg");
    let mut output = unhex(fields[0].1);
    let checkpoints = &fields[1..];
    assert_eq!(checkpoints.len(), 3 * 100);
    let range = max - min + 1;
    let mut outlen = max;
    for (j, v) in checkpoints.chunks(3).enumerate() {
        assert_eq!([v[0].0, v[1].0, v[2].0], ["COUNT", "Outputlen", "Output"]);
        assert_eq!(v[0].1, j.to_string());
        for _ in 0..1000 {
            let mut msg = [0u8; 16];
            let n = output.len().min(16);
            msg[..n].copy_from_slice(&output[..n]);
            output = vec![0; outlen];
            xof(&msg, &mut output);
            let right = u16::from_be_bytes([output[outlen - 2], output[outlen - 1]]) as usize;
            outlen = min + right % range;
        }
        assert_eq!(output.len() * 8, v[1].1.parse::<usize>().unwrap());
        assert_eq!(output, unhex(v[2].1));
    }
}

macro_rules! shake {
    ($name:ident, $xof:ident, $file:literal, $out:literal, $short:literal, $long:literal, $variable:literal, $min:literal, $max:literal) => {
        mod $name {
            use super::*;

            #[test]
            fn short_messages() {
                let n = check_shake_messages(
                    include_str!(concat!(
                        "../../vectors/nist-cavp/shake/",
                        $file,
                        "ShortMsg.rsp"
                    )),
                    $out,
                    $xof::digest,
                );
                assert_eq!(n, $short);
            }

            #[test]
            fn long_messages() {
                let n = check_shake_messages(
                    include_str!(concat!(
                        "../../vectors/nist-cavp/shake/",
                        $file,
                        "LongMsg.rsp"
                    )),
                    $out,
                    $xof::digest,
                );
                assert_eq!(n, $long);
            }

            #[test]
            fn variable_output() {
                let n = check_shake_variable(
                    include_str!(concat!(
                        "../../vectors/nist-cavp/shake/",
                        $file,
                        "VariableOut.rsp"
                    )),
                    $xof::digest,
                );
                assert_eq!(n, $variable);
            }

            #[test]
            fn monte_carlo() {
                check_shake_monte_carlo(
                    include_str!(concat!(
                        "../../vectors/nist-cavp/shake/",
                        $file,
                        "Monte.rsp"
                    )),
                    $min,
                    $max,
                    $xof::digest,
                );
            }
        }
    };
}

shake!(shake128, Shake128, "SHAKE128", 16, 337, 100, 1126, 16, 140);
shake!(shake256, Shake256, "SHAKE256", 32, 273, 100, 1246, 2, 250);
