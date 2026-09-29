//! HMAC-SHA-256.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput};
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hmac::Hmac;

use crate::{SIZES, VG};

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

    let key = [0x0b; 32];
    // With the baseline ISA's implementation (every CPU feature masked off),
    // which `hmac-sha256` runs too on CPUs without the SHA extensions.
    let mut g = c.benchmark_group("hmac-sha256-baseline");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut h = Hmac::<Sha256>::__with_features(black_box(&key), 0);
                h.update(black_box(&data));
                h.finalize()
            })
        });
    }
    g.finish();
}
