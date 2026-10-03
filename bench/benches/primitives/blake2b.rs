//! BLAKE2b.

use criterion::Criterion;

pub const USES: &[&str] = &["blake2b", "blake2"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::blake2b::Blake2b512;

    use crate::{hash_group, hash_verify_group};
    let md = MessageDigest::from_name("BLAKE2B512").unwrap();
    hash_group(c, "blake2b-512", Blake2b512::digest, md);
    // Unkeyed, as rust-openssl has no keyed BLAKE2 (`EVP_MAC`): `verify`
    // takes the same time keyed, after one more block.
    hash_verify_group(
        c,
        "blake2b-512-verify",
        Blake2b512::digest,
        |data, expected| {
            let mut h = Blake2b512::new();
            h.update(data);
            h.verify(expected).is_ok()
        },
        md,
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
)))]
pub fn bench(_: &mut Criterion) {}
