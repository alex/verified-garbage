//! HMAC-MD5 (RFC 2202, Section 2).

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::md5::Md5;

#[test]
fn hmac_md5() {
    let cases = super::cases("2. Test Cases for HMAC-MD5", "3. Test Cases for HMAC-SHA-1");
    super::check::<Md5>(&cases);
}
