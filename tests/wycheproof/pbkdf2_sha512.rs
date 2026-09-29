//! PBKDF2-HMAC-SHA-512 (`PbkdfTest` vectors).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::pbkdf2::pbkdf2_hmac;

use crate::pbkdf2::check_with;
use crate::require_vectors;

#[test]
fn pbkdf2_hmac_sha512_vectors() {
    require_vectors!();
    check_with("pbkdf2_hmacsha512_test.json", pbkdf2_hmac::<Sha512>);
}
