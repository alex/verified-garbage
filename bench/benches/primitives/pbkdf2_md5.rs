//! PBKDF2-HMAC-MD5.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["pbkdf2_md5", "hmac_md5", "md5"];

/// PBKDF2-HMAC-MD5 of a 32-byte password, deriving one block, with the
/// sizes as the iteration counts.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::md5::Md5;
    use verified_garbage::pbkdf2::pbkdf2_hmac;

    crate::pbkdf2_group(
        c,
        "pbkdf2-hmac-md5",
        pbkdf2_hmac::<Md5>,
        MessageDigest::md5(),
        16,
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
