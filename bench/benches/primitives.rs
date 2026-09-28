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

fn sha256(c: &mut Criterion) {
    hash_group(c, "sha256", Sha256::digest, MessageDigest::sha256());
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

#[cfg(target_arch = "x86_64")]
fn sha3(c: &mut Criterion) {
    use verified_garbage::hashes::sha3::{Sha3_224, Sha3_256, Sha3_384, Sha3_512, Shake128, Shake256};
    hash_group(c, "sha3-224", Sha3_224::digest, MessageDigest::sha3_224());
    hash_group(c, "sha3-256", Sha3_256::digest, MessageDigest::sha3_256());
    hash_group(c, "sha3-384", Sha3_384::digest, MessageDigest::sha3_384());
    hash_group(c, "sha3-512", Sha3_512::digest, MessageDigest::sha3_512());
    xof_group(c, "shake128", Shake128::digest, MessageDigest::shake_128());
    xof_group(c, "shake256", Shake256::digest, MessageDigest::shake_256());
}

#[cfg(not(target_arch = "x86_64"))]
fn sha3(_: &mut Criterion) {}

/// Benchmarks the extendable-output function `vg` against OpenSSL's `md`,
/// with 32 bytes of output.
#[cfg(target_arch = "x86_64")]
fn xof_group(c: &mut Criterion, name: &str, vg: fn(&[u8], &mut [u8]), md: MessageDigest) {
    use openssl::hash::Hasher;
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mut out = [0u8; 32];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| vg(black_box(&data), &mut out))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut h = Hasher::new(md).unwrap();
                h.update(black_box(&data)).unwrap();
                h.finish_xof(&mut out).unwrap();
            })
        });
    }
    g.finish();
}

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
}

criterion_group!(benches, chacha20, md5, sha1, sha256, sha3, sha512, hmac_sha256);
criterion_main!(benches);
