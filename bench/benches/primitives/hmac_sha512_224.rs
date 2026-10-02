//! HMAC-SHA-512/224.

use criterion::Criterion;

pub const USES: &[&str] = &["hmac_sha512_224", "sha512_224", "sha512"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha512_224::Sha512_224;
    use verified_garbage::hmac::Hmac;

    let md = MessageDigest::from_name("SHA512-224").unwrap();
    crate::hmac_group(c, "hmac-sha512-224", Hmac::<Sha512_224>::mac, md);
    crate::hmac_verify_group::<Sha512_224>(c, "hmac-sha512-224-verify", md);
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
