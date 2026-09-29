//! PBKDF2-HMAC-SHA-512/256 against its definition.

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha512_256;

#[test]
fn pbkdf2_hmac_sha512_256() {
    super::check::<Sha512_256>();
}
