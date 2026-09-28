//! SHA-1.

use criterion::Criterion;

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha1::Sha1;

    use crate::hash_group;
    hash_group(c, "sha1", Sha1::digest, MessageDigest::sha1());
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
