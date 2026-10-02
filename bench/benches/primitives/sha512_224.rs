//! SHA-512/224.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha512_224::Sha512_224;

use crate::hash_group;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["sha512_224", "sha512"];

pub fn bench(c: &mut Criterion) {
    let md = MessageDigest::from_name("SHA512-224").unwrap();
    hash_group(c, "sha512-224", Sha512_224::digest, md);
}
