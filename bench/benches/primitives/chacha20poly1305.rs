//! ChaCha20-Poly1305.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["chacha20poly1305", "chacha20", "poly1305"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, encrypt_aead};
    use verified_garbage::chacha20poly1305::ChaCha20Poly1305;

    use crate::{OPENSSL, SIZES, VG};
    let key = [0x42; 32];
    let nonce = [0x24; 12];
    let aad = [0x11; 16];
    let mut g = c.benchmark_group("chacha20poly1305");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let mut data = vec![0u8; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                ChaCha20Poly1305::new(black_box(&key)).encrypt_in_place(
                    black_box(&nonce),
                    black_box(&aad),
                    black_box(&mut data),
                )
            })
        });
        let mut tag = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                encrypt_aead(
                    Cipher::chacha20_poly1305(),
                    black_box(&key),
                    Some(black_box(&nonce)),
                    black_box(&aad),
                    black_box(&data),
                    &mut tag,
                )
                .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
