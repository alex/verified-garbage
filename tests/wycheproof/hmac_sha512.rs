//! HMAC-SHA-512 (`MacTest` vectors).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::hmac::Hmac;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha512() {
    require_vectors!();
    check("hmac_sha512_test.json", Hmac::<Sha512>::new);
}
