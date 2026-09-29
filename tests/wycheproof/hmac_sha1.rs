//! HMAC-SHA-1 (`MacTest` vectors).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha1::Sha1;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha1() {
    require_vectors!();
    check::<Sha1>("hmac_sha1_test.json");
}
