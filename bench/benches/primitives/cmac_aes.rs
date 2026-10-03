//! AES-CMAC.

use criterion::Criterion;

pub const USES: &[&str] = &["cmac_aes", "aes"];

/// The MAC of a message with each AES key width (setup included), computed and
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

    for (bits, key_len, cipher) in [
        (128, 16, Cipher::aes_128_cbc()),
        (192, 24, Cipher::aes_192_cbc()),
        (256, 32, Cipher::aes_256_cbc()),
    ] {
        let key = vec![0x42; key_len];
        let pkey = PKey::cmac(&cipher, &key).unwrap();
        let mut g = c.benchmark_group(format!("aes-{bits}-cmac"));
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

        let mut g = c.benchmark_group(format!("aes-{bits}-cmac-verify"));
        for size in SIZES {
            g.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            let mac = AesCmac::mac(&key, &data).unwrap();
            let mut reference = [0; 16];
            let mut signer = Signer::new_without_digest(&pkey).unwrap();
            assert_eq!(signer.sign_oneshot(&mut reference, &data).unwrap(), 16);
            assert_eq!(reference, mac);
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
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
