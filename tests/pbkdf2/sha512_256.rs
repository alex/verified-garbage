//! PBKDF2-HMAC-SHA-512/256 against its definition.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha512_256::Sha512_256;
use verified_garbage::pbkdf2::pbkdf2_hmac;

#[test]
fn pbkdf2_hmac_sha512_256() {
    super::check::<Sha512_256>(pbkdf2_hmac::<Sha512_256>);
}
