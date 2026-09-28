//! SHA-384: every message length from 0 to 128 bytes, 128 long messages
//! (from 227 to 12800 bytes) and the Monte Carlo test.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use super::{check_messages, check_monte_carlo};
use verified_garbage::hashes::sha384::Sha384;

/// Every message length from 0 to 128 bytes.
#[test]
fn short_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha512/SHA384ShortMsg.rsp"),
        Sha384::digest,
    );
    assert_eq!(n, 129);
}

#[test]
fn long_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha512/SHA384LongMsg.rsp"),
        Sha384::digest,
    );
    assert_eq!(n, 128);
}

/// The SHAVS Monte Carlo test.
#[test]
fn monte_carlo() {
    check_monte_carlo(
        include_str!("../../vectors/nist-cavp/sha512/SHA384Monte.rsp"),
        Sha384::digest,
    );
}
