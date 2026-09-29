//! PBKDF2-HMAC-SHA-256.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["pbkdf2_sha256", "hmac_sha256", "sha256"];

/// PBKDF2-HMAC-SHA-256 of a 32-byte key (one block), with the sizes as the
/// iteration counts.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;
    use std::num::NonZeroU32;

    use criterion::{BenchmarkId, Throughput};
    use openssl::hash::MessageDigest;

    use crate::{OPENSSL, SIZES, VG};
    let password = [0x0b; 32];
    let salt = [0x5a; 16];
    let mut g = c.benchmark_group("pbkdf2-hmac-sha256");
    for iterations in SIZES {
        g.throughput(Throughput::Elements(iterations as u64));
        let mut out = [0u8; 32];
        let n = NonZeroU32::new(iterations as u32).unwrap();
        g.bench_function(BenchmarkId::new(VG, iterations), |b| {
            b.iter(|| {
                verified_garbage::pbkdf2::pbkdf2_hmac_sha256(
                    black_box(&password),
                    black_box(&salt),
                    n,
                    &mut out,
                )
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, iterations), |b| {
            b.iter(|| {
                openssl::pkcs5::pbkdf2_hmac(
                    black_box(&password),
                    black_box(&salt),
                    iterations,
                    MessageDigest::sha256(),
                    &mut out,
                )
                .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
