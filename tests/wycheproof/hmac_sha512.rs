//! HMAC-SHA-512 (`MacTest` vectors).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha512;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha512() {
    require_vectors!();
    check::<Sha512>("hmac_sha512_test.json");
}
