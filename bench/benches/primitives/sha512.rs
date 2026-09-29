//! SHA-512.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["sha512"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha512::Sha512;

    use crate::hash_group;
    hash_group(c, "sha512", Sha512::digest, MessageDigest::sha512());
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
