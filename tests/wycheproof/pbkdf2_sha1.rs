//! PBKDF2-HMAC-SHA-1 (`PbkdfTest` vectors).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use verified_garbage::hashes::sha1::Sha1;
use verified_garbage::pbkdf2::pbkdf2_hmac;

use crate::pbkdf2::check_with;
use crate::require_vectors;

#[test]
fn pbkdf2_hmac_sha1_vectors() {
    require_vectors!();
    check_with("pbkdf2_hmacsha1_test.json", pbkdf2_hmac::<Sha1>);
}
