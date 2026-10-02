//! HMAC-SHA-224.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["hmac_sha224", "sha224", "sha256"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha224::Sha224;
    use verified_garbage::hmac::Hmac;

    crate::hmac_group(
        c,
        "hmac-sha224",
        Hmac::<Sha224>::mac,
        MessageDigest::sha224(),
    );
    crate::hmac_verify_group::<Sha224>(c, "hmac-sha224-verify", MessageDigest::sha224());
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
