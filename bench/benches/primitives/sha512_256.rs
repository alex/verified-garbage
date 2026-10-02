//! SHA-512/256.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha512_256::Sha512_256;

use crate::hash_group;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["sha512_256", "sha512"];

pub fn bench(c: &mut Criterion) {
    let md = MessageDigest::from_name("SHA512-256").unwrap();
    hash_group(c, "sha512-256", Sha512_256::digest, md);
}
