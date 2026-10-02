//! HMAC-SHA-512/256.

use criterion::Criterion;

pub const USES: &[&str] = &["hmac_sha512_256", "sha512_256", "sha512"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha512_256::Sha512_256;
    use verified_garbage::hmac::Hmac;

    let md = MessageDigest::from_name("SHA512-256").unwrap();
    crate::hmac_group(c, "hmac-sha512-256", Hmac::<Sha512_256>::mac, md);
    crate::hmac_verify_group::<Sha512_256>(c, "hmac-sha512-256-verify", md);
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
