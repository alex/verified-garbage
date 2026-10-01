//! AES-CMAC.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`): this one and those it calls.
pub const USES: &[&str] = &["cmac_aes", "aes"];

/// The MAC of a message with a 16-byte key (setup included), computed and
/// verified.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::pkey::PKey;
    use openssl::sign::Signer;
    use openssl::symm::Cipher;
    use verified_garbage::cmac::aes::AesCmac;

    use crate::{OPENSSL, SIZES, VG};

    let key = [0x42; 16];
    let pkey = PKey::cmac(&Cipher::aes_128_cbc(), &key).unwrap();
    let mut g = c.benchmark_group("aes-128-cmac");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| AesCmac::mac(black_box(&key), black_box(&data)).unwrap())
        });
        let mut out = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new_without_digest(&pkey).unwrap();
                s.sign_oneshot(&mut out, black_box(&data)).unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("aes-128-cmac-verify");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mac = AesCmac::mac(&key, &data).unwrap();
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut m = AesCmac::new(black_box(&key)).unwrap();
                m.update(black_box(&data));
                m.verify(black_box(&mac)).unwrap()
            })
        });
        let mut out = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new_without_digest(&pkey).unwrap();
                let n = s.sign_oneshot(&mut out, black_box(&data)).unwrap();
                assert!(openssl::memcmp::eq(&out[..n], black_box(&mac)))
            })
        });
    }
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
