//! PBKDF2-HMAC-SHA-256.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["pbkdf2_sha256", "hmac_sha256", "sha256"];

/// PBKDF2-HMAC-SHA-256 of a 32-byte key (one block), with the sizes as the
/// iteration counts.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::pbkdf2::pbkdf2_hmac_sha256;

    crate::pbkdf2_group(
        c,
        "pbkdf2-hmac-sha256",
        pbkdf2_hmac_sha256,
        MessageDigest::sha256(),
        32,
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
