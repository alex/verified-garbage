//! ML-KEM-768: key generation from a seed, encapsulation and decapsulation.
//!
//! OpenSSL implements ML-KEM from version 3.5, which the runners' OpenSSL
//! (3.0) predates, and rust-openssl has no encapsulation API, so there is
//! nothing of OpenSSL's to compare with: these benchmark this library alone.
//! The ids' sizes are the bytes of the output (the keys, the ciphertext and
//! the shared secret key).

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["mlkem768", "mlkem", "sha3"];

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use verified_garbage::mlkem768::DecapsulationKey768;

    use crate::VG;
    let seed = [0x42; 64];
    let dk = DecapsulationKey768::from_seed(&seed).unwrap();
    let ek = dk.encapsulation_key();
    let (_, ct) = ek.encapsulate().unwrap();
    let mut g = c.benchmark_group("mlkem768_keygen");
    g.bench_function(BenchmarkId::new(VG, 1184 + 64), |b| {
        b.iter(|| DecapsulationKey768::from_seed(black_box(&seed)).unwrap())
    });
    g.finish();
    let mut g = c.benchmark_group("mlkem768_encaps");
    g.bench_function(BenchmarkId::new(VG, 1088 + 32), |b| {
        b.iter(|| black_box(ek).encapsulate().unwrap())
    });
    g.finish();
    let mut g = c.benchmark_group("mlkem768_decaps");
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| dk.decapsulate(black_box(&ct)).unwrap())
    });
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
