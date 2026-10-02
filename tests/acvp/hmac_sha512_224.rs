//! HMAC-SHA-512/224 (`HMAC-SHA2-512-224-1.0`), with keys longer than a block among
//! them.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha512::Sha512_224;

use crate::hmac::check;

#[test]
fn hmac_sha512_224() {
    check::<Sha512_224>(include_str!(
        "../../vectors/nist-acvp/HMAC-SHA2-512-224-1.0/internalProjection.json"
    ));
}
