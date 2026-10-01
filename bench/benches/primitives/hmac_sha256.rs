//! HMAC-SHA-256.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hmac::Hmac;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["hmac_sha256", "sha256"];

pub fn bench(c: &mut Criterion) {
    crate::hmac_group(
        c,
        "hmac-sha256",
        Hmac::<Sha256>::mac,
        MessageDigest::sha256(),
    );
    crate::hmac_verify_group::<Sha256>(c, "hmac-sha256-verify", MessageDigest::sha256());
}
