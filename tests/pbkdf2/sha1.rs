//! PBKDF2-HMAC-SHA-1 against its definition.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::hashes::sha1::Sha1;
use verified_garbage::pbkdf2::pbkdf2_hmac;

#[test]
fn pbkdf2_hmac_sha1() {
    super::check::<Sha1>(pbkdf2_hmac::<Sha1>);
}
