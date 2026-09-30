//! BLAKE2b.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["blake2b", "blake2"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::blake2b::Blake2b512;

    use crate::hash_group;
    let md = MessageDigest::from_name("BLAKE2B512").unwrap();
    hash_group(c, "blake2b-512", Blake2b512::digest, md);
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
