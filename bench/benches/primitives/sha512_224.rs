//! SHA-512/224.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha512_224::Sha512_224;

use crate::hash_group;

pub const USES: &[&str] = &["sha512_224", "sha512"];

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
    let md = MessageDigest::from_name("SHA512-224").unwrap();
    hash_group(c, "sha512-224", Sha512_224::digest, md);
}
