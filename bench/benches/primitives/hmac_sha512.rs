//! HMAC-SHA-512.

use criterion::Criterion;

pub const USES: &[&str] = &["hmac_sha512", "sha512"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha512::Sha512;
    use verified_garbage::hmac::Hmac;

    crate::hmac_group(
        c,
        "hmac-sha512",
        Hmac::<Sha512>::mac,
        MessageDigest::sha512(),
    );
    crate::hmac_verify_group::<Sha512>(c, "hmac-sha512-verify", MessageDigest::sha512());
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
