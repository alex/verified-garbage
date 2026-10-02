//! HMAC-SHA-384 (`HMAC-SHA2-384-1.0`), with keys longer than a block among
//! them.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha384::Sha384;

use crate::hmac::check;

#[test]
fn hmac_sha384() {
    check::<Sha384>(include_str!(
        "../../vectors/nist-acvp/HMAC-SHA2-384-1.0/internalProjection.json"
    ));
}
