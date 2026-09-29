//! PBKDF2-HMAC-SHA-256 against its definition.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use verified_garbage::hashes::sha256::Sha256;

#[test]
fn pbkdf2_hmac_sha256() {
    super::check::<Sha256>();
}
