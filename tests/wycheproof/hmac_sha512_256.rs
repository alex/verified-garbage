//! HMAC-SHA-512/256 (`MacTest` vectors).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use verified_garbage::hashes::sha512::Sha512_256;
use verified_garbage::hmac::Hmac;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha512_256() {
    require_vectors!();
    check("hmac_sha512_256_test.json", Hmac::<Sha512_256>::new);
}
