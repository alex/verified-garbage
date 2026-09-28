//! HMAC.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput};
use openssl::hash::MessageDigest;
use openssl::pkey::PKey;
use openssl::sign::Signer;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hmac::Hmac;

use crate::{OPENSSL, SIZES, VG};

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["hmac", "sha256"];

pub fn bench(c: &mut Criterion) {
    let key = [0x0b; 32];
    let pkey = PKey::hmac(&key).unwrap();
    let mut g = c.benchmark_group("hmac-sha256");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| Hmac::<Sha256>::mac(black_box(&key), black_box(&data)))
        });
        let mut out = [0u8; 32];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new(MessageDigest::sha256(), &pkey).unwrap();
                s.sign_oneshot(&mut out, black_box(&data)).unwrap()
            })
        });
    }
    g.finish();

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
