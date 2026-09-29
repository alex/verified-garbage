//! HMAC-SHA-512/256 (`MacTest` vectors).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha512_256;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha512_256() {
    require_vectors!();
    check::<Sha512_256>("hmac_sha512_256_test.json");
}
