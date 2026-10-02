//! The benchmarks of ML-KEM, for each parameter set: key generation from a
//! seed, encapsulation and decapsulation.
//!
//! OpenSSL implements ML-KEM from version 3.5, which the runners' OpenSSL
//! (3.0) predates, and rust-openssl has no encapsulation API, so there is
//! nothing of OpenSSL's to compare with: these benchmark this library alone.
//! The ids' sizes are the bytes of the output (the keys, the ciphertext and
//! the shared secret key).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

/// Runs, in `$c`, the benchmarks of the module `verified_garbage::$module`
/// and its key types, in groups named after the module.
macro_rules! mlkem_bench {
    ($c:expr, verified_garbage::$module:ident, $DecapsulationKey:ident, $EncapsulationKey:ident) => {{
        use std::hint::black_box;

        use criterion::BenchmarkId;
        use verified_garbage::$module::{$DecapsulationKey, $EncapsulationKey};

        use crate::VG;
        let c: &mut criterion::Criterion = $c;
        let seed = [0x42; 64];
        let dk = $DecapsulationKey::from_seed(&seed).unwrap();
        let ek = dk.encapsulation_key();
        let (_, ct) = ek.encapsulate().unwrap();
        let mut g = c.benchmark_group(concat!(stringify!($module), "_keygen"));
        g.bench_function(BenchmarkId::new(VG, $EncapsulationKey::SIZE + 64), |b| {
            b.iter(|| $DecapsulationKey::from_seed(black_box(&seed)).unwrap())
        });
        g.finish();
        let mut g = c.benchmark_group(concat!(stringify!($module), "_encaps"));
        g.bench_function(
            BenchmarkId::new(VG, $EncapsulationKey::CIPHERTEXT_SIZE + 32),
            |b| b.iter(|| black_box(ek).encapsulate().unwrap()),
        );
        g.finish();
        let mut g = c.benchmark_group(concat!(stringify!($module), "_decaps"));
        g.bench_function(BenchmarkId::new(VG, 32), |b| {
            b.iter(|| dk.decapsulate(black_box(&ct)).unwrap())
        });
        g.finish();
    }};
}

pub(crate) use mlkem_bench;
