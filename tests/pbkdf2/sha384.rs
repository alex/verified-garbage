//! PBKDF2-HMAC-SHA-384 against its definition.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha512::Sha384;
use verified_garbage::pbkdf2::pbkdf2_hmac;

#[test]
fn pbkdf2_hmac_sha384() {
    super::check::<Sha384>(pbkdf2_hmac::<Sha384>);
}
