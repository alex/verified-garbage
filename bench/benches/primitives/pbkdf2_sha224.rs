//! PBKDF2-HMAC-SHA-224.

use criterion::Criterion;

pub const USES: &[&str] = &["pbkdf2_sha224", "hmac_sha224", "sha224", "sha256"];

/// PBKDF2-HMAC-SHA-224 of a 32-byte password, deriving one block, with the
/// sizes as the iteration counts.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha224::Sha224;
    use verified_garbage::pbkdf2::pbkdf2_hmac;

    crate::pbkdf2_group(
        c,
        "pbkdf2-hmac-sha224",
        pbkdf2_hmac::<Sha224>,
        MessageDigest::sha224(),
        28,
    );
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
