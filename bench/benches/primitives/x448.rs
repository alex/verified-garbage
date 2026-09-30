//! X448.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["x448"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::derive::Deriver;
    use openssl::pkey::{Id, PKey};
    use verified_garbage::x448::{PrivateKey, x448};

    use crate::{OPENSSL, VG};
    let private = [0x42; 56];
    let peer = PrivateKey::from_bytes(&[0x24; 56]).public_key();
    let mut g = c.benchmark_group("x448");
    // One Diffie-Hellman: a shared secret from a private key and the peer's
    // public key. The ids' size is the bytes of the shared secret.
    g.bench_function(BenchmarkId::new(VG, 56), |b| {
        b.iter(|| {
            PrivateKey::from_bytes(black_box(&private))
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 56), |b| {
        b.iter(|| {
            let key = PKey::private_key_from_raw_bytes(black_box(&private), Id::X448).unwrap();
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer), Id::X448).unwrap();
            let mut d = Deriver::new(&key).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.finish();

    let mut g = c.benchmark_group("x448_raw");
    g.bench_function(BenchmarkId::new(VG, 56), |b| {
        b.iter(|| x448(black_box(&private), black_box(&peer)))
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 56), |b| {
        b.iter(|| {
            let key = PKey::private_key_from_raw_bytes(black_box(&private), Id::X448).unwrap();
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer), Id::X448).unwrap();
            let mut d = Deriver::new(&key).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.finish();

    let mut g = c.benchmark_group("x448_public_key");
    g.bench_function(BenchmarkId::new(VG, 56), |b| {
        b.iter(|| PrivateKey::from_bytes(black_box(&private)).public_key())
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 56), |b| {
        b.iter(|| {
            PKey::private_key_from_raw_bytes(black_box(&private), Id::X448)
                .unwrap()
                .raw_public_key()
                .unwrap()
        })
    });
    g.finish();

    let mut g = c.benchmark_group("x448_generate");
    g.bench_function(BenchmarkId::new(VG, 56), |b| {
        b.iter(|| *PrivateKey::generate().unwrap().as_bytes())
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 56), |b| {
        b.iter(|| PKey::generate_x448().unwrap().raw_private_key().unwrap())
    });
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
)))]
pub fn bench(_: &mut Criterion) {}
