//! BLAKE2s.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["blake2s", "blake2"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86"))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::blake2s::Blake2s256;

    use crate::hash_group;
    let md = MessageDigest::from_name("BLAKE2S256").unwrap();
    hash_group(c, "blake2s-256", Blake2s256::digest, md);
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86")))]
pub fn bench(_: &mut Criterion) {}
