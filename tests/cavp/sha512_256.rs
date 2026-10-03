//! SHA-512/256: every message length from 0 to 128 bytes, 128 long messages
//! (from 227 to 12800 bytes) and the Monte Carlo test.

use super::{check_messages, check_monte_carlo};
use verified_garbage::hashes::sha512_256::Sha512_256;

/// Every message length from 0 to 128 bytes.
#[test]
fn short_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha512/SHA512_256ShortMsg.rsp"),
        Sha512_256::digest,
    );
    assert_eq!(n, 129);
}

#[test]
fn long_messages() {
    let n = check_messages(
        include_str!("../../vectors/nist-cavp/sha512/SHA512_256LongMsg.rsp"),
        Sha512_256::digest,
    );
    assert_eq!(n, 128);
}

/// The SHAVS Monte Carlo test.
#[test]
fn monte_carlo() {
    check_monte_carlo(
        include_str!("../../vectors/nist-cavp/sha512/SHA512_256Monte.rsp"),
        Sha512_256::digest,
    );
}
