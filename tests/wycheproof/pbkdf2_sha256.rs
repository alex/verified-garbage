//! PBKDF2-HMAC-SHA-256 (`PbkdfTest` vectors).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::pbkdf2::{pbkdf2_hmac, pbkdf2_hmac_sha256};

use crate::pbkdf2::check_with;
use crate::require_vectors;

#[test]
fn pbkdf2_hmac_sha256_vectors() {
    require_vectors!();
    check_with("pbkdf2_hmacsha256_test.json", pbkdf2_hmac_sha256);
    check_with("pbkdf2_hmacsha256_test.json", pbkdf2_hmac::<Sha256>);
}
