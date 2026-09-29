//! PBKDF2-HMAC-SHA-384 (`PbkdfTest` vectors).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha384;

use crate::pbkdf2::check;
use crate::require_vectors;

#[test]
fn pbkdf2_hmac_sha384_vectors() {
    require_vectors!();
    check::<Sha384>("pbkdf2_hmacsha384_test.json");
}
