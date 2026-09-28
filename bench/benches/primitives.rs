//! Throughput of each public API, next to the same operation in OpenSSL
//! (through rust-openssl), at a few message sizes.
//!
//! Every benchmark is one complete operation (setup included), as a caller
//! of either library would do it. Benchmark ids are
//! `<primitive>/<library>/<bytes>`; `ci/bench_compare.py` relies on this.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use openssl::hash::{MessageDigest, hash};
use openssl::pkey::PKey;
use openssl::sign::Signer;
use openssl::symm::{Cipher, Crypter, Mode};
use verified_garbage::chacha20::ChaCha20;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hmac::Hmac;

const SIZES: [usize; 3] = [64, 1024, 16384];

const VG: &str = "verified-garbage";
const OPENSSL: &str = "openssl";

fn chacha20(c: &mut Criterion) {
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

/// Benchmarks the hash `vg` against OpenSSL's `md`.
fn hash_group<const N: usize>(
    c: &mut Criterion,
    name: &str,
    vg: fn(&[u8]) -> [u8; N],
    md: MessageDigest,
) {
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| vg(black_box(&data)))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| hash(md, black_box(&data)).unwrap())
        });
    }
    g.finish();
}

/// Benchmarks the hash `vg` alone.
fn vg_group<const N: usize>(c: &mut Criterion, name: &str, vg: fn(&[u8]) -> [u8; N]) {
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| vg(black_box(&data)))
        });
    }
    g.finish();
}

fn sha256(c: &mut Criterion) {
    hash_group(c, "sha256", Sha256::digest, MessageDigest::sha256());
    // The implementation for the baseline ISA (every CPU feature masked
    // off), which `sha256` runs too on CPUs without the SHA extensions.
    vg_group(c, "sha256-baseline", |m| {
        let mut h = Sha256::__with_features(0);
        h.update(m);
        h.finalize()
    });
}

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn sha512(c: &mut Criterion) {
    use verified_garbage::hashes::sha512::Sha512;
    hash_group(c, "sha512", Sha512::digest, MessageDigest::sha512());
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
fn sha512(_: &mut Criterion) {}

#[cfg(target_arch = "x86_64")]
fn md5(c: &mut Criterion) {
    use verified_garbage::hashes::md5::Md5;
    hash_group(c, "md5", Md5::digest, MessageDigest::md5());
}

#[cfg(not(target_arch = "x86_64"))]
fn md5(_: &mut Criterion) {}

#[cfg(target_arch = "x86_64")]
fn sha1(c: &mut Criterion) {
    use verified_garbage::hashes::sha1::Sha1;
    hash_group(c, "sha1", Sha1::digest, MessageDigest::sha1());
}

#[cfg(not(target_arch = "x86_64"))]
fn sha1(_: &mut Criterion) {}

fn hmac_sha256(c: &mut Criterion) {
    let key = [0x0b; 32];
    let pkey = PKey::hmac(&key).unwrap();
    let mut g = c.benchmark_group("hmac-sha256");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| Hmac::<Sha256>::mac(black_box(&key), black_box(&data)))
        });
        let mut out = [0u8; 32];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new(MessageDigest::sha256(), &pkey).unwrap();
                s.sign_oneshot(&mut out, black_box(&data)).unwrap()
            })
        });
    }
    g.finish();

    // With the baseline ISA's implementation (every CPU feature masked off),
    // which `hmac-sha256` runs too on CPUs without the SHA extensions.
    let mut g = c.benchmark_group("hmac-sha256-baseline");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut h = Hmac::<Sha256>::__with_features(black_box(&key), 0);
                h.update(black_box(&data));
                h.finalize()
            })
        });
    }
    g.finish();
}

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn poly1305(c: &mut Criterion) {
    use openssl::pkey::Id;
    use verified_garbage::poly1305::Poly1305;
    let key = [0x0b; 32];
    let mut g = c.benchmark_group("poly1305");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| Poly1305::mac(black_box(&key), black_box(&data)))
        });
        let mut out = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let pkey = PKey::private_key_from_raw_bytes(black_box(&key), Id::POLY1305).unwrap();
                let mut s = Signer::new_without_digest(&pkey).unwrap();
                s.sign_oneshot(&mut out, black_box(&data)).unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
fn poly1305(_: &mut Criterion) {}

#[cfg(target_arch = "x86_64")]
fn chacha20poly1305(c: &mut Criterion) {
    use openssl::symm::encrypt_aead;
    use verified_garbage::chacha20poly1305::ChaCha20Poly1305;
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
fn chacha20poly1305(_: &mut Criterion) {}

criterion_group!(
    benches,
    chacha20,
    chacha20poly1305,
    md5,
    poly1305,
    sha1,
    sha256,
    sha512,
    hmac_sha256
);
criterion_main!(benches);
