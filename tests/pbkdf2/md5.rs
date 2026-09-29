//! PBKDF2-HMAC-MD5 against its definition.

#![cfg(target_arch = "x86_64")]

use verified_garbage::hashes::md5::Md5;
use verified_garbage::pbkdf2::pbkdf2_hmac;

#[test]
fn pbkdf2_hmac_md5() {
    super::check::<Md5>(pbkdf2_hmac::<Md5>);
}
