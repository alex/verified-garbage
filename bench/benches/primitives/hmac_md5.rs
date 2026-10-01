//! HMAC-MD5.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["hmac_md5", "md5"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::md5::Md5;
    use verified_garbage::hmac::Hmac;

    crate::hmac_group(c, "hmac-md5", Hmac::<Md5>::mac, MessageDigest::md5());
    crate::hmac_verify_group::<Md5>(c, "hmac-md5-verify", MessageDigest::md5());
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
