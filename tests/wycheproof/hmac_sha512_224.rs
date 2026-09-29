//! HMAC-SHA-512/224 (`MacTest` vectors).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha512_224;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha512_224() {
    require_vectors!();
    check::<Sha512_224>("hmac_sha512_224_test.json");
}
