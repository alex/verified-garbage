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
    use verified_garbage::hashes::sha256::Sha256;
    use verified_garbage::pbkdf2::{__pbkdf2_hmac_with_features, pbkdf2_hmac_sha256};

    use crate::{SIZES, VG};

    crate::pbkdf2_group(
        c,
        "pbkdf2-hmac-sha256",
        pbkdf2_hmac_sha256,
        MessageDigest::sha256(),
        32,
    );

    // The implementation for the baseline ISA (every CPU feature masked
    // off), which `pbkdf2-hmac-sha256` runs too on CPUs without the SHA
    // extensions.
    let password = [0x0b; 32];
    let salt = [0x5a; 16];
    let mut g = c.benchmark_group("pbkdf2-hmac-sha256-baseline");
    for iterations in SIZES {
        g.throughput(Throughput::Elements(iterations as u64));
        let mut out = [0u8; 32];
        let n = NonZeroU32::new(iterations as u32).unwrap();
        g.bench_function(BenchmarkId::new(VG, iterations), |b| {
            b.iter(|| {
                __pbkdf2_hmac_with_features::<Sha256>(
                    black_box(&password),
                    black_box(&salt),
                    n,
                    &mut out,
                    0,
                )
            })
        });
    }
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
