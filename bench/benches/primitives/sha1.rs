//! SHA-1.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha1::Sha1;

use crate::hash_group;

pub const USES: &[&str] = &["sha1"];

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    hash_group(c, "sha1", Sha1::digest, MessageDigest::sha1());
}
