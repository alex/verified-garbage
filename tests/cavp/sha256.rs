//! SHA-256: every message length from 0 to 64 bytes, 64 long messages and the
//! Monte Carlo test.

use super::{check_messages, check_monte_carlo};
use verified_garbage::hashes::sha256::Sha256;

/// Every message length from 0 to 64 bytes.
#[test]
fn short_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha256/SHA256ShortMsg.rsp"),
        Sha256::digest,
    );
    assert_eq!(n, 65);
}

#[test]
fn long_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha256/SHA256LongMsg.rsp"),
        Sha256::digest,
    );
    assert_eq!(n, 64);
}

/// The SHAVS Monte Carlo test.
#[test]
fn monte_carlo() {
    check_monte_carlo(
        include_str!("../../vectors/nist-cavp/sha256/SHA256Monte.rsp"),
        Sha256::digest,
    );
}
