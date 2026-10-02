//! TDEA-CMAC.

use criterion::Criterion;

pub const USES: &[&str] = &["cmac_triple_des"];

/// The MAC of a message with a 24-byte (three-key) key (setup included),
/// computed and verified.
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
    use verified_garbage::cmac::triple_des::TripleDesCmac;

    use crate::{OPENSSL, SIZES, VG};

    let key: [u8; 24] = core::array::from_fn(|i| 0x42 ^ i as u8);
    let pkey = PKey::cmac(&Cipher::des_ede3_cbc(), &key).unwrap();
    let mut g = c.benchmark_group("tdes-cmac");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| TripleDesCmac::mac(black_box(&key), black_box(&data)).unwrap())
        });
        let mut out = [0u8; 8];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new_without_digest(&pkey).unwrap();
                s.sign_oneshot(&mut out, black_box(&data)).unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("tdes-cmac-verify");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mac = TripleDesCmac::mac(&key, &data).unwrap();
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut m = TripleDesCmac::new(black_box(&key)).unwrap();
                m.update(black_box(&data));
                m.verify(black_box(&mac)).unwrap()
            })
        });
        let mut out = [0u8; 8];
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
