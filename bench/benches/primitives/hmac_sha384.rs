//! HMAC-SHA-384.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["hmac_sha384", "sha512"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha512::Sha384;
    use verified_garbage::hmac::Hmac;

    crate::hmac_group(
        c,
        "hmac-sha384",
        Hmac::<Sha384>::mac,
        MessageDigest::sha384(),
    );
    crate::hmac_verify_group::<Sha384>(c, "hmac-sha384-verify", MessageDigest::sha384());
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
