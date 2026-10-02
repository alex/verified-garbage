//! PBKDF2-HMAC-SHA-384 (`PbkdfTest` vectors).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::pbkdf2::pbkdf2_hmac;

use crate::pbkdf2::check_with;
use crate::require_vectors;

#[test]
fn pbkdf2_hmac_sha384_vectors() {
    require_vectors!();
    check_with("pbkdf2_hmacsha384_test.json", pbkdf2_hmac::<Sha384>);
}
