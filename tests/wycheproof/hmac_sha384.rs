//! HMAC-SHA-384 (`MacTest` vectors).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use verified_garbage::hashes::sha512::Sha384;
use verified_garbage::hmac::Hmac;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha384() {
    require_vectors!();
    check("hmac_sha384_test.json", Hmac::<Sha384>::new);
}
