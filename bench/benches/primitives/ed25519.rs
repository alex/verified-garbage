//! Ed25519 key derivation, signing, and verification beside OpenSSL.

use criterion::Criterion;

pub const USES: &[&str] = &["ed25519", "sha512"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::pkey::{Id, PKey};
    use openssl::sign::{Signer, Verifier};
    use verified_garbage::ed25519::{SigningKey, VerifyingKey};

    use crate::{OPENSSL, SIZES, VG};

    let seed = [0x42; 32];
    let key = SigningKey::from_seed(&seed);
    let public = VerifyingKey::from_bytes(key.verifying_key().as_bytes());
    let openssl_key = PKey::private_key_from_raw_bytes(&seed, Id::ED25519).unwrap();
    let openssl_public = PKey::public_key_from_raw_bytes(public.as_bytes(), Id::ED25519).unwrap();

    let mut g = c.benchmark_group("ed25519_keygen");
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| SigningKey::from_seed(black_box(&seed)))
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            PKey::private_key_from_raw_bytes(black_box(&seed), Id::ED25519)
                .unwrap()
                .raw_public_key()
                .unwrap()
        })
    });
    g.finish();

    let mut g = c.benchmark_group("ed25519_sign");
    for size in SIZES {
        let message = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| key.sign(black_box(&message)))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                Signer::new_without_digest(&openssl_key)
                    .unwrap()
                    .sign_oneshot_to_vec(black_box(&message))
                    .unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("ed25519_verify");
    for size in SIZES {
        let message = vec![0x5a; size];
        let signature = key.sign(&message);
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                public
                    .verify(black_box(&message), black_box(&signature))
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                Verifier::new_without_digest(&openssl_public)
                    .unwrap()
                    .verify_oneshot(black_box(&signature), black_box(&message))
                    .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
