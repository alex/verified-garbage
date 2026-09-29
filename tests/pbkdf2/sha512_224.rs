//! PBKDF2-HMAC-SHA-512/224 against its definition.

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha512_224;

#[test]
fn pbkdf2_hmac_sha512_224() {
    super::check::<Sha512_224>();
}
