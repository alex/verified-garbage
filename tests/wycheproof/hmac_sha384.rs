//! HMAC-SHA-384 (`MacTest` vectors).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha384;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha384() {
    require_vectors!();
    check::<Sha384>("hmac_sha384_test.json");
}
