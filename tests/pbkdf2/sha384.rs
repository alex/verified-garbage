//! PBKDF2-HMAC-SHA-384 against its definition.

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha384;

#[test]
fn pbkdf2_hmac_sha384() {
    super::check::<Sha384>();
}
