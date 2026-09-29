//! HMAC-SHA-256.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hmac::Hmac;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
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
}
