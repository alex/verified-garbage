//! SHA-512.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha512::Sha512;

use crate::hash_group;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["sha512"];

pub fn bench(c: &mut Criterion) {
    hash_group(c, "sha512", Sha512::digest, MessageDigest::sha512());
}
