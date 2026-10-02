//! PBKDF2-HMAC-SHA-512/256.

use criterion::Criterion;

pub const USES: &[&str] = &[
    "pbkdf2_sha512_256",
    "hmac_sha512_256",
    "sha512_256",
    "sha512",
];

/// PBKDF2-HMAC-SHA-512/256 of a 32-byte password, deriving one block, with the
/// sizes as the iteration counts.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha512_256::Sha512_256;
    use verified_garbage::pbkdf2::pbkdf2_hmac;

    crate::pbkdf2_group(
        c,
        "pbkdf2-hmac-sha512-256",
        pbkdf2_hmac::<Sha512_256>,
        MessageDigest::from_name("SHA512-256").unwrap(),
        32,
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
