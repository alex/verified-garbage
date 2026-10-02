//! RC2-CBC, including initialization, update, and unpadded finalization.

use criterion::Criterion;

pub const USES: &[&str] = &["rc2_cbc", "rc2"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::provider::Provider;
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::rc2_cbc::{Rc2CbcDecryptor, Rc2CbcEncryptor};

    use crate::{OPENSSL, SIZES, VG};

    // RC2 is in OpenSSL 3's legacy provider; retain the default provider
    // for the other algorithms benchmarked by this process.
    let _legacy = Provider::try_load(None, "legacy", true).unwrap();
    let key = [0x42; 16];
    let iv = [0x24; 8];
    for (name, mode) in [
        ("rc2-cbc-encrypt", Mode::Encrypt),
        ("rc2-cbc-decrypt", Mode::Decrypt),
    ] {
        let mut g = c.benchmark_group(name);
        for size in SIZES {
            g.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            g.bench_function(BenchmarkId::new(VG, size), |b| match mode {
                Mode::Encrypt => b.iter(|| {
                    let mut ctx = Rc2CbcEncryptor::new(black_box(&key), black_box(&iv)).unwrap();
                    let output = ctx.update(black_box(&data));
                    black_box(ctx.finalize().unwrap());
                    black_box(output)
                }),
                Mode::Decrypt => b.iter(|| {
                    let mut ctx = Rc2CbcDecryptor::new_with_effective_bits(
                        black_box(&key),
                        black_box(&iv),
                        128,
                    )
                    .unwrap();
                    let output = ctx.update(black_box(&data));
                    black_box(ctx.finalize().unwrap());
                    black_box(output)
                }),
            });
            let mut output = vec![0; size + 8];
            g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = Crypter::new(
                        Cipher::rc2_cbc(),
                        mode,
                        black_box(&key),
                        Some(black_box(&iv)),
                    )
                    .unwrap();
                    ctx.pad(false);
                    let n = ctx.update(black_box(&data), &mut output).unwrap();
                    let n = n + ctx.finalize(&mut output[n..]).unwrap();
                    black_box(&output[..n]);
                })
            });
        }
        g.finish();
    }
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
