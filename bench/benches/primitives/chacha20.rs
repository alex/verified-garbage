//! ChaCha20.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput};
use openssl::symm::{Cipher, Crypter, Mode};
use verified_garbage::chacha20::ChaCha20;

use crate::{OPENSSL, SIZES, VG};

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["chacha20"];

pub fn bench(c: &mut Criterion) {
    let key = [0x42; 32];
    let nonce = [0x24; 16];
    let mut g = c.benchmark_group("chacha20");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let mut data = vec![0u8; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut c = ChaCha20::new(black_box(&key), black_box(&nonce));
                c.apply_keystream(black_box(&mut data));
            })
        });
        // OpenSSL's ChaCha20 takes the same 16-byte nonce (counter ‖ nonce).
        let mut out = vec![0u8; size + Cipher::chacha20().block_size()];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut c = Crypter::new(
                    Cipher::chacha20(),
                    Mode::Encrypt,
                    black_box(&key),
                    Some(black_box(&nonce)),
                )
                .unwrap();
                c.update(black_box(&data), &mut out).unwrap();
            })
        });
    }
    g.finish();
}
