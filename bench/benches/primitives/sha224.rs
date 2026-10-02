//! SHA-224.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha224::Sha224;

use crate::hash_group;

pub const USES: &[&str] = &["sha224", "sha256"];

pub fn bench(c: &mut Criterion) {
    hash_group(c, "sha224", Sha224::digest, MessageDigest::sha224());
}
