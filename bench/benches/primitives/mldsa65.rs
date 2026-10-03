//! ML-DSA-65: key generation from a seed, signing and verification.
//!
//! OpenSSL implements ML-DSA from version 3.5; the runners use 3.0.
//! Enable `openssl-mldsa` on a supported host for the comparison. The ids'
//! sizes are the output bytes for keygen/sign and message bytes for verify.

use criterion::Criterion;

pub const USES: &[&str] = &["mldsa65", "mldsa_common", "mldsa", "sha3"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use verified_garbage::mldsa65::SigningKey65;

    use crate::VG;
    let seed = [0x42; 32];
    let key = SigningKey65::from_seed(&seed).unwrap();
    let msg = [0x5a; 64];
    let sig = key.sign(&msg, b"").unwrap();
    #[cfg(feature = "openssl-mldsa")]
    let (openssl_key, openssl_public) = {
        use openssl::pkey::{KeyType, PKey};
        use openssl::sign::{Signer, Verifier};

        let key_type = KeyType::ML_DSA_65;
        let openssl_key = PKey::private_key_from_seed(None, key_type, None, &seed).unwrap();
        let public = openssl_key.raw_public_key().unwrap();
        assert_eq!(public.as_slice(), key.verifying_key().as_bytes());
        let openssl_public =
            PKey::public_key_from_raw_bytes_ex(None, key_type, None, &public).unwrap();
        assert!(
            Verifier::new_without_digest(&openssl_public)
                .unwrap()
                .verify_oneshot(&sig, &msg)
                .unwrap()
        );
        let openssl_sig = Signer::new_without_digest(&openssl_key)
            .unwrap()
            .sign_oneshot_to_vec(&msg)
            .unwrap();
        key.verifying_key()
            .verify(&msg, b"", openssl_sig.as_slice().try_into().unwrap())
            .unwrap();
        (openssl_key, openssl_public)
    };
    let mut g = c.benchmark_group("mldsa65_keygen");
    g.bench_function(BenchmarkId::new(VG, 1952 + 32), |b| {
        b.iter(|| SigningKey65::from_seed(black_box(&seed)).unwrap())
    });
    #[cfg(feature = "openssl-mldsa")]
    g.bench_function(BenchmarkId::new(crate::OPENSSL, 1984), |b| {
        b.iter(|| {
            openssl::pkey::PKey::private_key_from_seed(
                None,
                openssl::pkey::KeyType::ML_DSA_65,
                None,
                black_box(&seed),
            )
            .unwrap()
            .raw_public_key()
            .unwrap()
        })
    });
    g.finish();
    let mut g = c.benchmark_group("mldsa65_sign");
    g.bench_function(BenchmarkId::new(VG, 3309), |b| {
        b.iter(|| key.sign(black_box(&msg), b"").unwrap())
    });
    #[cfg(feature = "openssl-mldsa")]
    g.bench_function(BenchmarkId::new(crate::OPENSSL, 3309), |b| {
        b.iter(|| {
            openssl::sign::Signer::new_without_digest(&openssl_key)
                .unwrap()
                .sign_oneshot_to_vec(black_box(&msg))
                .unwrap()
        })
    });
    g.finish();
    let mut g = c.benchmark_group("mldsa65_verify");
    g.bench_function(BenchmarkId::new(VG, 64), |b| {
        b.iter(|| {
            key.verifying_key()
                .verify(black_box(&msg), b"", &sig)
                .unwrap()
        })
    });
    #[cfg(feature = "openssl-mldsa")]
    g.bench_function(BenchmarkId::new(crate::OPENSSL, 64), |b| {
        b.iter(|| {
            assert!(
                openssl::sign::Verifier::new_without_digest(&openssl_public)
                    .unwrap()
                    .verify_oneshot(black_box(&sig), black_box(&msg))
                    .unwrap()
            )
        })
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
