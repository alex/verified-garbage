//! PBKDF2-HMAC-SHA-1 against its definition.

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha1::Sha1;

#[test]
fn pbkdf2_hmac_sha1() {
    super::check::<Sha1>();
}
