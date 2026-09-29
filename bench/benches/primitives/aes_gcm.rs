//! AES-GCM.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["aes_gcm", "aes", "gcm"];

/// One-shot AES-GCM encryption and decryption (setup included), and
/// streaming encryption, with a 16-byte key, a 12-byte nonce and 16 bytes of
/// additional data.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode, decrypt_aead, encrypt_aead};
    use verified_garbage::aes_gcm::{AesGcm, AesGcmStream, Direction};

    use crate::{OPENSSL, SIZES, VG};

    let key = [0x42; 16];
    let nonce = [0x24; 12];
    let aad = [0x5a; 16];
    let cipher = Cipher::aes_128_gcm();
    for size in SIZES {
        let data = vec![0u8; size];
        let mut buf = data.clone();
        let tag = AesGcm::new(&key)
            .unwrap()
            .encrypt(&nonce, &aad, &mut buf)
            .unwrap();
        let ct = buf.clone();

        let mut g = c.benchmark_group("aes-128-gcm-encrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesGcm::new(black_box(&key)).unwrap();
                k.encrypt(black_box(&nonce), black_box(&aad), black_box(&mut buf))
                    .unwrap()
            })
        });
        let mut t = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                encrypt_aead(
                    cipher,
                    black_box(&key),
                    Some(black_box(&nonce)),
                    black_box(&aad),
                    black_box(&data),
                    &mut t,
                )
                .unwrap()
            })
        });
        g.finish();

        let mut g = c.benchmark_group("aes-128-gcm-decrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                buf.copy_from_slice(&ct);
                let k = AesGcm::new(black_box(&key)).unwrap();
                k.decrypt(
                    black_box(&nonce),
                    black_box(&aad),
                    black_box(&mut buf),
                    &tag,
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                decrypt_aead(
                    cipher,
                    black_box(&key),
                    Some(black_box(&nonce)),
                    black_box(&aad),
                    black_box(&ct),
                    &tag,
                )
                .unwrap()
            })
        });
        g.finish();

        let mut g = c.benchmark_group("aes-128-gcm-stream");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut s =
                    AesGcmStream::new(black_box(&key), black_box(&nonce), Direction::Encrypt)
                        .unwrap();
                s.update_aad(black_box(&aad)).unwrap();
                s.update(black_box(&mut buf)).unwrap();
                s.finalize().unwrap()
            })
        });
        let mut out = vec![0u8; size + cipher.block_size()];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Crypter::new(
                    cipher,
                    Mode::Encrypt,
                    black_box(&key),
                    Some(black_box(&nonce)),
                )
                .unwrap();
                s.aad_update(black_box(&aad)).unwrap();
                let n = s.update(black_box(&data), &mut out).unwrap();
                s.finalize(&mut out[n..]).unwrap();
                s.get_tag(&mut t).unwrap();
            })
        });
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
