//! HMAC-SHA-256.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hmac::Hmac;

pub const USES: &[&str] = &["hmac_sha256", "sha256"];

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    crate::hmac_group(
        c,
        "hmac-sha256",
        Hmac::<Sha256>::mac,
        MessageDigest::sha256(),
    );
    crate::hmac_verify_group::<Sha256>(c, "hmac-sha256-verify", MessageDigest::sha256());
}
