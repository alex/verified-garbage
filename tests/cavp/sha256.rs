//! SHA-256: every message length from 0 to 64 bytes, 64 long messages and the
//! Monte Carlo test, with the best implementation for this CPU and with the
//! baseline ISA's.

use super::{check_messages, check_monte_carlo};
use verified_garbage::hashes::sha256::Sha256;

/// A SHA-256 digest function.
type Digest256 = fn(&[u8]) -> [u8; 32];

/// SHA-256 with every implementation this CPU can run: the best one, and the
/// one for the baseline ISA (with every CPU feature masked off).
const SHA256: [Digest256; 2] = [Sha256::digest, |m| {
    let mut h = Sha256::__with_features(0);
    h.update(m);
    h.finalize()
}];

/// Every message length from 0 to 64 bytes.
#[test]
fn short_messages() {
    for digest in SHA256 {
        let n = check_messages(
            include_str!("../../vectors/nist-cavp/sha256/SHA256ShortMsg.rsp"),
            digest,
        );
        assert_eq!(n, 65);
    }
}

#[test]
fn long_messages() {
    for digest in SHA256 {
        let n = check_messages(
            include_str!("../../vectors/nist-cavp/sha256/SHA256LongMsg.rsp"),
            digest,
        );
        assert_eq!(n, 64);
    }
}

/// The SHAVS Monte Carlo test.
#[test]
fn monte_carlo() {
    for digest in SHA256 {
        check_monte_carlo(
            include_str!("../../vectors/nist-cavp/sha256/SHA256Monte.rsp"),
            digest,
        );
    }
}
