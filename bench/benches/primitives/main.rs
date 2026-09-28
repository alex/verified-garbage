//! Throughput of each public API, next to the same operation in OpenSSL
//! (through rust-openssl), at a few message sizes.
//!
//! Every benchmark is one complete operation (setup included), as a caller
//! of either library would do it. Benchmark ids are
//! `<primitive>/<library>/<bytes>`; `ci/bench_compare.py` relies on this.
//!
//! Each algorithm's benchmarks are in a module of their own, whose `bench`
//! runs them (and does nothing on architectures the algorithm doesn't
//! support yet), so that adding one adds a file.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use openssl::hash::{MessageDigest, hash};

mod chacha20;
mod chacha20poly1305;
mod hmac;
mod md5;
mod pbkdf2;
mod poly1305;
mod scrypt;
mod sha1;
mod sha256;
mod sha3;
mod sha512;

const SIZES: [usize; 3] = [64, 1024, 16384];

const VG: &str = "verified-garbage";
const OPENSSL: &str = "openssl";

/// Benchmarks the hash `vg` against OpenSSL's `md`.
pub(crate) fn hash_group<const N: usize>(
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
pub(crate) fn vg_group<const N: usize>(c: &mut Criterion, name: &str, vg: fn(&[u8]) -> [u8; N]) {
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

fn all(c: &mut Criterion) {
    chacha20::bench(c);
    chacha20poly1305::bench(c);
    hmac::bench(c);
    md5::bench(c);
    pbkdf2::bench(c);
    poly1305::bench(c);
    scrypt::bench(c);
    sha1::bench(c);
    sha256::bench(c);
    sha3::bench(c);
    sha512::bench(c);
}

criterion_group!(benches, all);
criterion_main!(benches);
