//! Raw RC4 initialization, in-place XOR and finalization, next to OpenSSL.

use criterion::Criterion;

pub const USES: &[&str] = &["rc4"];

#[cfg(target_arch = "aarch64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::provider::Provider;
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::rc4::Rc4;

    use crate::{OPENSSL, SIZES, VG};

    // Retain the default provider for the process's other benchmarks.
    let _legacy = Provider::try_load(None, "legacy", true).unwrap();
    let key = [0x42; 16];
    let mut g = c.benchmark_group("rc4");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let mut data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut ctx = Rc4::new(black_box(&key)).unwrap();
                ctx.apply_keystream(black_box(&mut data));
                ctx.finalize();
            })
        });
        let mut output = vec![0; size + Cipher::rc4().block_size()];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut ctx =
                    Crypter::new(Cipher::rc4(), Mode::Encrypt, black_box(&key), None).unwrap();
                let n = ctx.update(black_box(&data), &mut output).unwrap();
                let n = n + ctx.finalize(&mut output[n..]).unwrap();
                black_box(&output[..n]);
            })
        });
    }
    g.finish();
}

#[cfg(not(target_arch = "aarch64"))]
pub fn bench(_: &mut Criterion) {}
