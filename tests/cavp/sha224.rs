//! SHA-224: every message length from 0 to 64 bytes, 64 long messages and the
//! Monte Carlo test.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use super::{check_messages, check_monte_carlo};
use verified_garbage::hashes::sha224::Sha224;

/// Every message length from 0 to 64 bytes.
#[test]
fn short_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha224/SHA224ShortMsg.rsp"),
        Sha224::digest,
    );
    assert_eq!(n, 65);
}

#[test]
fn long_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha224/SHA224LongMsg.rsp"),
        Sha224::digest,
    );
    assert_eq!(n, 64);
}

/// The SHAVS Monte Carlo test.
#[test]
fn monte_carlo() {
    check_monte_carlo(
        include_str!("../../vectors/nist-cavp/sha224/SHA224Monte.rsp"),
        Sha224::digest,
    );
}
