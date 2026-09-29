//! PBKDF2-HMAC-SHA-512/224 against its definition.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::hashes::sha512::Sha512_224;
use verified_garbage::pbkdf2::pbkdf2_hmac;

#[test]
fn pbkdf2_hmac_sha512_224() {
    super::check::<Sha512_224>(pbkdf2_hmac::<Sha512_224>);
}
