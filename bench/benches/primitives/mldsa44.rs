//! ML-DSA-44: key generation from a seed, signing and verification.
//!
//! OpenSSL implements ML-DSA from version 3.5, which the runners' OpenSSL
//! (3.0) predates, so there is nothing of OpenSSL's to compare with: these
//! benchmark this library alone. The ids' sizes are the bytes of the output
//! (the public key and its seed, the signature) or, for verification, of
//! the message.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["mldsa44", "mldsa_common", "mldsa", "sha3"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use verified_garbage::mldsa44::SigningKey44;

    use crate::VG;
    let seed = [0x42; 32];
    let key = SigningKey44::from_seed(&seed).unwrap();
    let msg = [0x5a; 64];
    let sig = key.sign(&msg, b"").unwrap();
    let mut g = c.benchmark_group("mldsa44_keygen");
    g.bench_function(BenchmarkId::new(VG, 1312 + 32), |b| {
        b.iter(|| SigningKey44::from_seed(black_box(&seed)).unwrap())
    });
    g.finish();
    let mut g = c.benchmark_group("mldsa44_sign");
    g.bench_function(BenchmarkId::new(VG, 2420), |b| {
        b.iter(|| key.sign(black_box(&msg), b"").unwrap())
    });
    g.finish();
    let mut g = c.benchmark_group("mldsa44_verify");
    g.bench_function(BenchmarkId::new(VG, 64), |b| {
        b.iter(|| {
            key.verifying_key()
                .verify(black_box(&msg), b"", &sig)
                .unwrap()
        })
    });
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
