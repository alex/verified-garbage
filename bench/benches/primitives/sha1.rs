//! SHA-1.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha1::Sha1;

use crate::hash_group;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["sha1"];

pub fn bench(c: &mut Criterion) {
    hash_group(c, "sha1", Sha1::digest, MessageDigest::sha1());
}
