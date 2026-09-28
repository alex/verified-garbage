//! SHA-256.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha256::Sha256;

use crate::{hash_group, vg_group};

pub fn bench(c: &mut Criterion) {
    hash_group(c, "sha256", Sha256::digest, MessageDigest::sha256());
    // The implementation for the baseline ISA (every CPU feature masked
    // off), which `sha256` runs too on CPUs without the SHA extensions.
    vg_group(c, "sha256-baseline", |m| {
        let mut h = Sha256::__with_features(0);
        h.update(m);
        h.finalize()
    });
}
