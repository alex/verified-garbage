//! SHA-256.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha256::Sha256;

use crate::hash_group;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["sha256"];

pub fn bench(c: &mut Criterion) {
    hash_group(c, "sha256", Sha256::digest, MessageDigest::sha256());
}
