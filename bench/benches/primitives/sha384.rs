//! SHA-384.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha384::Sha384;

use crate::hash_group;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["sha384", "sha512"];

pub fn bench(c: &mut Criterion) {
    hash_group(c, "sha384", Sha384::digest, MessageDigest::sha384());
}
