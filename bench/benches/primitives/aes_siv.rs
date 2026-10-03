//! AES-SIV.

use criterion::Criterion;

pub const USES: &[&str] = &["aes_siv", "aes", "cmac_aes"];

/// One-shot AES-SIV encryption and decryption (setup included), with a
/// 32-byte key (AES-128 for each half) and one 16-byte associated-data
/// component. OpenSSL's runs through its `AES-128-SIV` cipher (fetched from
/// the default provider), which rust-openssl has no shortcut for.
#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::aes_siv::AesSiv;

    use crate::{OPENSSL, SIZES, VG};

    let key = [0x42; 32];
    let aad = [0x5a; 16];
    let cipher = Cipher::fetch(None, "AES-128-SIV", None).unwrap();
    for size in SIZES {
        let data = vec![0u8; size];
        let mut buf = data.clone();
        let tag = AesSiv::new(&key)
            .unwrap()
            .encrypt_in_place(&[&aad], &mut buf)
            .unwrap();
        let ct = buf.clone();
        let mut out = vec![0u8; size];

        let mut g = c.benchmark_group("aes-128-siv-encrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesSiv::new(black_box(&key)).unwrap();
                k.encrypt_in_place(&[black_box(&aad)], black_box(&mut buf))
                    .unwrap()
            })
        });
        let mut t = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut ctx = CipherCtx::new().unwrap();
                ctx.encrypt_init(Some(&cipher), Some(black_box(&key)), None)
                    .unwrap();
                ctx.cipher_update(black_box(&aad), None).unwrap();
                ctx.cipher_update(black_box(&data), Some(&mut out)).unwrap();
                ctx.cipher_final(&mut []).unwrap();
                ctx.tag(&mut t).unwrap();
            })
        });
        g.finish();

        let mut g = c.benchmark_group("aes-128-siv-decrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                buf.copy_from_slice(&ct);
                let k = AesSiv::new(black_box(&key)).unwrap();
                k.decrypt_in_place(&[black_box(&aad)], black_box(&mut buf), &tag)
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut ctx = CipherCtx::new().unwrap();
                ctx.decrypt_init(Some(&cipher), Some(black_box(&key)), None)
                    .unwrap();
                ctx.set_tag(&tag).unwrap();
                ctx.cipher_update(black_box(&aad), None).unwrap();
                ctx.cipher_update(black_box(&ct), Some(&mut out)).unwrap();
                ctx.cipher_final(&mut []).unwrap();
            })
        });
        g.finish();
    }
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
