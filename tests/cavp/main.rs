//! NIST CAVP (<https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program>)
//! known-answer tests.
//!
//! The response files are vendored under `vectors/nist-cavp/` (see
//! `vectors/sources.toml` for where each one comes from) and compiled into
//! the test binary, so these tests always run. Every vector of every file is
//! checked.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::sha256::Sha256;

/// The `key = value` lines of a CAVP response file, in order, without the
/// comments, blank lines and `[L = ...]` section headers.
fn fields(text: &str) -> Vec<(&str, &str)> {
    text.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#') && !l.starts_with('['))
        .map(|l| l.split_once(" = ").unwrap())
        .collect()
}

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// Checks every `Len`/`Msg`/`MD` vector of a SHA-256 message test file, and
/// returns how many there were.
fn check_messages(text: &str) -> usize {
    assert!(text.contains("[L = 32]"));
    let fields = fields(text);
    assert_eq!(fields.len() % 3, 0);
    for v in fields.chunks(3) {
        assert_eq!([v[0].0, v[1].0, v[2].0], ["Len", "Msg", "MD"]);
        // `Len` is in bits; the zero-length message is written as `Msg = 00`.
        let len: usize = v[0].1.parse().unwrap();
        assert_eq!(len % 8, 0);
        let msg = unhex(v[1].1);
        assert_eq!(Sha256::digest(&msg[..len / 8])[..], unhex(v[2].1));
    }
    fields.len() / 3
}

/// Every message length from 0 to 64 bytes.
#[test]
fn sha256_short_messages() {
    let n = check_messages(include_str!(
        "../../vectors/nist-cavp/sha256/SHA256ShortMsg.rsp"
    ));
    assert_eq!(n, 65);
}

#[test]
fn sha256_long_messages() {
    let n = check_messages(include_str!(
        "../../vectors/nist-cavp/sha256/SHA256LongMsg.rsp"
    ));
    assert_eq!(n, 64);
}

/// The SHAVS Monte Carlo test: 100 checkpoints, each after 1000 iterations
/// of hashing the concatenation of the previous three digests.
#[test]
fn sha256_monte_carlo() {
    let text = include_str!("../../vectors/nist-cavp/sha256/SHA256Monte.rsp");
    assert!(text.contains("[L = 32]"));
    let fields = fields(text);
    assert_eq!(fields[0].0, "Seed");
    let mut seed: [u8; 32] = unhex(fields[0].1).try_into().unwrap();
    let checkpoints = &fields[1..];
    assert_eq!(checkpoints.len(), 2 * 100);
    for (j, v) in checkpoints.chunks(2).enumerate() {
        assert_eq!([v[0].0, v[1].0], ["COUNT", "MD"]);
        assert_eq!(v[0].1, j.to_string());
        let mut md = [seed; 3];
        for _ in 3..1003 {
            let mut m = [0u8; 96];
            m[..32].copy_from_slice(&md[0]);
            m[32..64].copy_from_slice(&md[1]);
            m[64..].copy_from_slice(&md[2]);
            md = [md[1], md[2], Sha256::digest(&m)];
        }
        seed = md[2];
        assert_eq!(seed[..], unhex(v[1].1));
    }
}
