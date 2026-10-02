//! PBKDF2-HMAC-SHA-512/224.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &[
    "pbkdf2_sha512_224",
    "hmac_sha512_224",
    "sha512_224",
    "sha512",
];

/// PBKDF2-HMAC-SHA-512/224 of a 32-byte password, deriving one block, with the
/// sizes as the iteration counts.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha512_224::Sha512_224;
    use verified_garbage::pbkdf2::pbkdf2_hmac;

    crate::pbkdf2_group(
        c,
        "pbkdf2-hmac-sha512-224",
        pbkdf2_hmac::<Sha512_224>,
        MessageDigest::from_name("SHA512-224").unwrap(),
        28,
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
