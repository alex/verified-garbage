//! scrypt.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["scrypt", "pbkdf2", "hmac", "sha256"];

/// scrypt with `r = 8` and `p = 1` (the RFC 7914 vectors' block size) at a
/// few costs `N`, deriving a 64-byte key. The ids' sizes are `N`.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use verified_garbage::scrypt::scrypt;

    use crate::{OPENSSL, VG};
    let mut g = c.benchmark_group("scrypt");
    g.sample_size(10);
    for n in [1024u64, 16384] {
        let mut out = [0u8; 64];
        g.bench_function(BenchmarkId::new(VG, n), |b| {
            b.iter(|| {
                scrypt(
                    black_box(b"password"),
                    black_box(b"NaCl"),
                    n,
                    8,
                    1,
                    usize::MAX,
                    &mut out,
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, n), |b| {
            b.iter(|| {
                openssl::pkcs5::scrypt(
                    black_box(b"password"),
                    black_box(b"NaCl"),
                    n,
                    8,
                    1,
                    u64::MAX,
                    &mut out,
                )
                .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
