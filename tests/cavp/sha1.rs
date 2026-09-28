//! SHA-1: every message length from 0 to 64 bytes, 64 long messages (from
//! 163 to 6400 bytes) and the Monte Carlo test.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use super::{check_messages, check_monte_carlo};
use verified_garbage::hashes::sha1::Sha1;

#[test]
fn short_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha1/SHA1ShortMsg.rsp"),
        Sha1::digest,
    );
    assert_eq!(n, 65);
}

#[test]
fn long_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha1/SHA1LongMsg.rsp"),
        Sha1::digest,
    );
    assert_eq!(n, 64);
}

#[test]
fn monte_carlo() {
    check_monte_carlo(
        include_str!("../../vectors/nist-cavp/sha1/SHA1Monte.rsp"),
        Sha1::digest,
    );
}
