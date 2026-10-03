//! HMAC-SHA-224 (`MacTest` vectors).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha224::Sha224;
use verified_garbage::hmac::Hmac;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha224() {
    require_vectors!();
    check("hmac_sha224_test.json", Hmac::<Sha224>::new);
}
