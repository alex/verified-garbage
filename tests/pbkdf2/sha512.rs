//! PBKDF2-HMAC-SHA-512 against its definition.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::pbkdf2::pbkdf2_hmac;

#[test]
fn pbkdf2_hmac_sha512() {
    super::check::<Sha512>(pbkdf2_hmac::<Sha512>);
}
