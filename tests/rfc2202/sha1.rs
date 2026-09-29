//! HMAC-SHA-1 (RFC 2202, Section 3).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::sha1::Sha1;

#[test]
fn hmac_sha1() {
    let cases = super::cases("3. Test Cases for HMAC-SHA-1", "4. Security Considerations");
    super::check::<Sha1>(&cases);
}
