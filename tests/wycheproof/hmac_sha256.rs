//! HMAC-SHA-256 (`MacTest` vectors).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hmac::Hmac;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha256() {
    require_vectors!();
    check("hmac_sha256_test.json", Hmac::<Sha256>::new);
}
