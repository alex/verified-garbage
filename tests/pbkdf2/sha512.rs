//! PBKDF2-HMAC-SHA-512 against its definition.

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha512;

#[test]
fn pbkdf2_hmac_sha512() {
    super::check::<Sha512>();
}
