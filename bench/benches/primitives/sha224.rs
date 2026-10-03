//! SHA-224.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha224::Sha224;

use crate::hash_group;

pub const USES: &[&str] = &["sha224", "sha256"];

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
    hash_group(c, "sha224", Sha224::digest, MessageDigest::sha224());
}
