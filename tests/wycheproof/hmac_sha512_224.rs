//! HMAC-SHA-512/224 (`MacTest` vectors).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha512::Sha512_224;
use verified_garbage::hmac::Hmac;

use crate::hmac::check;
use crate::require_vectors;

#[test]
fn hmac_sha512_224() {
    require_vectors!();
    check("hmac_sha512_224_test.json", Hmac::<Sha512_224>::new);
}
