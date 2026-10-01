//! Triple DES ECB, including key expansion and unpadded streaming.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["triple_des_ecb", "triple_des"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::nid::Nid;
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::triple_des_ecb::{Direction, TripleDesEcb};

    use crate::{OPENSSL, SIZES, VG};

    let key: Vec<_> = (0..24).map(|i| (17 * i + 3) as u8).collect();
    for (key_len, cipher) in [
        (16, Cipher::from_nid(Nid::DES_EDE_ECB).unwrap()),
        (24, Cipher::des_ede3_ecb()),
    ] {
        for (operation, direction, mode) in [
            ("encrypt", Direction::Encrypt, Mode::Encrypt),
            ("decrypt", Direction::Decrypt, Mode::Decrypt),
        ] {
            let mut group = c.benchmark_group(format!("3des-ecb-{operation}-{key_len}"));
            for size in SIZES {
                group.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                group.bench_function(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        let mut ctx =
                            TripleDesEcb::init(black_box(&key[..key_len]), direction).unwrap();
                        let output = ctx.update(black_box(&data));
                        black_box(ctx.finalize().unwrap());
                        black_box(output)
                    })
                });
                let mut output = vec![0; size + 8];
                group.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                    b.iter(|| {
                        let mut ctx =
                            Crypter::new(cipher, mode, black_box(&key[..key_len]), None).unwrap();
                        ctx.pad(false);
                        let n = ctx.update(black_box(&data), &mut output).unwrap();
                        let n = n + ctx.finalize(&mut output[n..]).unwrap();
                        black_box(&output[..n]);
                    })
                });
            }
            group.finish();
        }
    }
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
