//! PBKDF2-HMAC-SHA-1 (`PbkdfTest` vectors).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha1::Sha1;

use crate::pbkdf2::check;
use crate::require_vectors;

#[test]
fn pbkdf2_hmac_sha1_vectors() {
    require_vectors!();
    check::<Sha1>("pbkdf2_hmacsha1_test.json");
}
