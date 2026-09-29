//! PBKDF2-HMAC-SHA-512 (`PbkdfTest` vectors).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha512;

use crate::pbkdf2::check;
use crate::require_vectors;

#[test]
fn pbkdf2_hmac_sha512_vectors() {
    require_vectors!();
    check::<Sha512>("pbkdf2_hmacsha512_test.json");
}
