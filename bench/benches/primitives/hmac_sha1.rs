//! HMAC-SHA-1.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["hmac_sha1", "sha1"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha1::Sha1;
    use verified_garbage::hmac::Hmac;

    crate::hmac_group(c, "hmac-sha1", Hmac::<Sha1>::mac, MessageDigest::sha1());
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
