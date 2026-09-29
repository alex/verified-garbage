//! MD5.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::md5::Md5;

use crate::hash_group;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["md5"];

pub fn bench(c: &mut Criterion) {
    hash_group(c, "md5", Md5::digest, MessageDigest::md5());
}
