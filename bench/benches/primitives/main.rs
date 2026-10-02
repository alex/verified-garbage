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
use openssl::pkey::PKey;
use openssl::sign::Signer;

mod aes_gcm;
mod argon2;
mod blake2b;
mod blake2s;
mod chacha20;
mod chacha20poly1305;
mod cmac_aes;
mod cmac_triple_des;
mod ed25519;
mod hmac_md5;
mod hmac_sha1;
mod hmac_sha224;
mod hmac_sha256;
mod hmac_sha384;
mod hmac_sha512;
mod hmac_sha512_224;
mod hmac_sha512_256;
mod md5;
mod mldsa44;
mod mldsa65;
mod mldsa87;
mod mlkem1024;
mod mlkem768;
mod pbkdf2_md5;
mod pbkdf2_sha1;
mod pbkdf2_sha224;
mod pbkdf2_sha256;
mod pbkdf2_sha384;
mod pbkdf2_sha512;
mod pbkdf2_sha512_224;
mod pbkdf2_sha512_256;
mod poly1305;
mod rc2_cbc;
mod scrypt;
mod sha1;
mod sha224;
mod sha256;
mod sha3;
mod sha384;
mod sha512;
mod sha512_224;
mod sha512_256;
mod triple_des_ecb;
mod x25519;
mod x448;

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

/// Benchmarks HMAC with the hash of `vg` and `md` (32-byte key) against
/// OpenSSL's.
pub(crate) fn hmac_group<O>(
    c: &mut Criterion,
    name: &str,
    vg: fn(&[u8], &[u8]) -> O,
    md: MessageDigest,
) {
    let key = [0x0b; 32];
    let pkey = PKey::hmac(&key).unwrap();
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| vg(black_box(&key), black_box(&data)))
        });
        let mut out = [0u8; 64];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new(md, &pkey).unwrap();
                s.sign_oneshot(&mut out, black_box(&data)).unwrap()
            })
        });
    }
    g.finish();
}

/// Benchmarks checking an HMAC with the hash `H` and `md` (32-byte key)
/// against OpenSSL's: computing the MAC of the data and comparing it with
/// the expected one in constant time (`Hmac::verify`; OpenSSL's
/// `CRYPTO_memcmp`).
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub(crate) fn hmac_verify_group<H: verified_garbage::hmac::HmacHash>(
    c: &mut Criterion,
    name: &str,
    md: MessageDigest,
) {
    use verified_garbage::hmac::Hmac;
    let key = [0x0b; 32];
    let pkey = PKey::hmac(&key).unwrap();
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mac = Hmac::<H>::mac(&key, &data);
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut h = Hmac::<H>::new(black_box(&key));
                h.update(black_box(&data));
                h.verify(black_box(mac.as_ref())).unwrap()
            })
        });
        let mut out = [0u8; 64];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new(md, &pkey).unwrap();
                let n = s.sign_oneshot(&mut out, black_box(&data)).unwrap();
                assert!(openssl::memcmp::eq(&out[..n], black_box(mac.as_ref())))
            })
        });
    }
    g.finish();
}

/// Benchmarks PBKDF2 with the hash of `vg` and `md` against OpenSSL's, of a
/// 32-byte password, deriving `len` bytes (a digest), with the sizes as the
/// iteration counts.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub(crate) fn pbkdf2_group(
    c: &mut Criterion,
    name: &str,
    vg: fn(&[u8], &[u8], std::num::NonZeroU32, &mut [u8]),
    md: MessageDigest,
    len: usize,
) {
    let password = [0x0b; 32];
    let salt = [0x5a; 16];
    let mut g = c.benchmark_group(name);
    for iterations in SIZES {
        g.throughput(Throughput::Elements(iterations as u64));
        let mut out = vec![0u8; len];
        let n = std::num::NonZeroU32::new(iterations as u32).unwrap();
        g.bench_function(BenchmarkId::new(VG, iterations), |b| {
            b.iter(|| vg(black_box(&password), black_box(&salt), n, &mut out))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, iterations), |b| {
            b.iter(|| {
                openssl::pkcs5::pbkdf2_hmac(
                    black_box(&password),
                    black_box(&salt),
                    iterations,
                    md,
                    &mut out,
                )
                .unwrap()
            })
        });
    }
    g.finish();
}

/// Each algorithm's `bench`, with the library modules whose code it runs
/// (its `USES`, which `ci/bench_arches.py` reads).
type Bench = (&'static [&'static str], fn(&mut Criterion));

const BENCHES: &[Bench] = &[
    (aes_gcm::USES, aes_gcm::bench),
    (blake2b::USES, blake2b::bench),
    (blake2s::USES, blake2s::bench),
    (chacha20::USES, chacha20::bench),
    (chacha20poly1305::USES, chacha20poly1305::bench),
    (cmac_aes::USES, cmac_aes::bench),
    (cmac_triple_des::USES, cmac_triple_des::bench),
    (hmac_md5::USES, hmac_md5::bench),
    (hmac_sha1::USES, hmac_sha1::bench),
    (hmac_sha224::USES, hmac_sha224::bench),
    (hmac_sha256::USES, hmac_sha256::bench),
    (hmac_sha384::USES, hmac_sha384::bench),
    (hmac_sha512::USES, hmac_sha512::bench),
    (hmac_sha512_224::USES, hmac_sha512_224::bench),
    (hmac_sha512_256::USES, hmac_sha512_256::bench),
    (md5::USES, md5::bench),
    (mldsa44::USES, mldsa44::bench),
    (mldsa65::USES, mldsa65::bench),
    (mldsa87::USES, mldsa87::bench),
    (mlkem1024::USES, mlkem1024::bench),
    (mlkem768::USES, mlkem768::bench),
    (pbkdf2_md5::USES, pbkdf2_md5::bench),
    (pbkdf2_sha1::USES, pbkdf2_sha1::bench),
    (pbkdf2_sha224::USES, pbkdf2_sha224::bench),
    (pbkdf2_sha256::USES, pbkdf2_sha256::bench),
    (pbkdf2_sha384::USES, pbkdf2_sha384::bench),
    (pbkdf2_sha512::USES, pbkdf2_sha512::bench),
    (pbkdf2_sha512_224::USES, pbkdf2_sha512_224::bench),
    (pbkdf2_sha512_256::USES, pbkdf2_sha512_256::bench),
    (poly1305::USES, poly1305::bench),
    (rc2_cbc::USES, rc2_cbc::bench),
    (triple_des_ecb::USES, triple_des_ecb::bench),
    (argon2::USES, argon2::bench),
    (scrypt::USES, scrypt::bench),
    (sha1::USES, sha1::bench),
    (sha224::USES, sha224::bench),
    (sha256::USES, sha256::bench),
    (sha3::USES, sha3::bench),
    (sha384::USES, sha384::bench),
    (sha512::USES, sha512::bench),
    (sha512_224::USES, sha512_224::bench),
    (sha512_256::USES, sha512_256::bench),
    (x25519::USES, x25519::bench),
    (x448::USES, x448::bench),
    (ed25519::USES, ed25519::bench),
];

/// Runs the benchmarks that use any of the modules in `$VG_BENCH_MODULES`
/// (space-separated), or every benchmark if it is unset or empty. The CI
/// selector requests all benchmarks for shared or unknown dependencies. An
/// unknown explicit module is an error, rather than silently running everything.
fn all(c: &mut Criterion) {
    let modules = std::env::var("VG_BENCH_MODULES").unwrap_or_default();
    let modules: Vec<&str> = modules.split_whitespace().collect();
    let used = |m: &&str| BENCHES.iter().any(|(uses, _)| uses.contains(m));
    assert!(
        modules.iter().all(used),
        "VG_BENCH_MODULES names a module absent from the benchmark registry"
    );
    let every = modules.is_empty();
    for (uses, bench) in BENCHES {
        if every || uses.iter().any(|u| modules.contains(u)) {
            bench(c);
        }
    }
}

criterion_group!(benches, all);
criterion_main!(benches);
