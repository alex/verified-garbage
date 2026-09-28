//! MD5.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["md5"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::md5::Md5;

    use crate::hash_group;
    hash_group(c, "md5", Md5::digest, MessageDigest::md5());
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
