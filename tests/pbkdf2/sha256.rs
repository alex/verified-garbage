//! PBKDF2-HMAC-SHA-256 against its definition.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::pbkdf2::pbkdf2_hmac;

#[test]
fn pbkdf2_hmac_sha256() {
    super::check::<Sha256>(pbkdf2_hmac::<Sha256>);
}

/// `pbkdf2_hmac_verify` accepts the derived key, and a key derived with a
/// length of its own (each is a prefix of the longer ones), and rejects any
/// other: with a bit flipped in its first, a middle or its last byte, with a
/// byte appended that is not the next one derived, from another password,
/// and an empty one.
#[cfg(feature = "alloc")]
#[test]
fn pbkdf2_hmac_sha256_verify() {
    use core::num::NonZeroU32;

    use verified_garbage::pbkdf2::{KeyMismatch, pbkdf2_hmac_verify};

    let c = NonZeroU32::new(3).unwrap();
    let verify = |expected: &[u8]| pbkdf2_hmac_verify::<Sha256>(b"password", b"salt", c, expected);
    let mut dk = [0u8; 41];
    pbkdf2_hmac::<Sha256>(b"password", b"salt", c, &mut dk);
    let mut longer = dk;
    let dk = &dk[..40];
    assert_eq!(verify(dk), Ok(()));
    for i in [0, 20, 39] {
        let mut bad = dk.to_vec();
        bad[i] ^= 1;
        assert_eq!(verify(&bad), Err(KeyMismatch));
    }
    assert_eq!(verify(&dk[..1]), Ok(()));
    assert_eq!(verify(&dk[..39]), Ok(()));
    assert_eq!(verify(&longer), Ok(()));
    longer[40] ^= 1;
    assert_eq!(verify(&longer), Err(KeyMismatch));
    assert_eq!(verify(&[]), Err(KeyMismatch));
    assert_eq!(
        pbkdf2_hmac_verify::<Sha256>(b"passwore", b"salt", c, dk),
        Err(KeyMismatch)
    );
    assert_eq!(KeyMismatch.to_string(), "PBKDF2 derived key does not match");
    let _: &dyn std::error::Error = &KeyMismatch;
    assert_eq!(format!("{KeyMismatch:?}"), "KeyMismatch");
}
