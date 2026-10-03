//! ECDSA over P-256 with SHA-256, and P-256 public keys, beside OpenSSL.

use criterion::Criterion;

pub const USES: &[&str] = &[
    "ecdsa_p256_sha256",
    "ecdsa_p256",
    "ec_p256",
    "hmac_sha256",
    "sha256",
];

/// Signing a message with SHA-256: deterministically (RFC 6979), and in
/// OpenSSL with a random `k` (its default); verifying a signature, with the
/// public key decoded and checked in each verification, as the verified
/// code does.
#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::ec::{EcGroup, EcKey, EcPoint, PointConversionForm};
    use openssl::ecdsa::EcdsaSig;
    use openssl::hash::MessageDigest;
    use openssl::nid::Nid;
    use openssl::pkey::PKey;
    use openssl::sign::{Signer, Verifier};
    use verified_garbage::ecdsa::{P256, SigningKey, VerifyingKey};

    use crate::{OPENSSL, SIZES, VG};

    let d = [0x42; 32];
    let key = SigningKey::<P256>::from_bytes(&d);
    let group = EcGroup::from_curve_name(Nid::X9_62_PRIME256V1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let d_bn = BigNum::from_slice(&d).unwrap();
    let mut public = EcPoint::new(&group).unwrap();
    public.mul_generator2(&group, &d_bn, &mut ctx).unwrap();
    let openssl_key =
        PKey::from_ec_key(EcKey::from_private_components(&group, &d_bn, &public).unwrap()).unwrap();

    let mut g = c.benchmark_group("ecdsa_p256_sha256_sign");
    for size in SIZES {
        let message = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| key.sign_sha256(black_box(&message)).unwrap())
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                Signer::new(MessageDigest::sha256(), &openssl_key)
                    .unwrap()
                    .sign_oneshot_to_vec(black_box(&message))
                    .unwrap()
            })
        });
    }
    g.finish();

    let q = key.public_key().unwrap();
    let verifying_key = VerifyingKey::<P256>::from_bytes(&q);
    let mut g = c.benchmark_group("ecdsa_p256_sha256_verify");
    for size in SIZES {
        let message = vec![0x5a; size];
        let sig = key.sign_sha256(&message).unwrap();
        let der = EcdsaSig::from_private_components(
            BigNum::from_slice(&sig[..32]).unwrap(),
            BigNum::from_slice(&sig[32..]).unwrap(),
        )
        .unwrap()
        .to_der()
        .unwrap();
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                verifying_key
                    .verify_sha256(black_box(&message), &sig)
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let point = EcPoint::from_bytes(&group, black_box(&q), &mut ctx).unwrap();
                let ec = EcKey::from_public_key(&group, &point).unwrap();
                ec.check_key().unwrap();
                let pkey = PKey::from_ec_key(ec).unwrap();
                let mut verifier = Verifier::new(MessageDigest::sha256(), &pkey).unwrap();
                assert!(verifier.verify_oneshot(&der, black_box(&message)).unwrap());
            })
        });
    }
    g.finish();

    // The public key of a private key, uncompressed: in OpenSSL, `[d]G` and
    // its encoding. The ids' size is the bytes of the public key.
    let mut g = c.benchmark_group("ec_p256_public_key");
    g.bench_function(BenchmarkId::new(VG, 65), |b| {
        b.iter(|| {
            SigningKey::<P256>::from_bytes(black_box(&d))
                .public_key()
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 65), |b| {
        b.iter(|| {
            let d = BigNum::from_slice(black_box(&d)).unwrap();
            let mut q = EcPoint::new(&group).unwrap();
            q.mul_generator2(&group, &d, &mut ctx).unwrap();
            q.to_bytes(&group, PointConversionForm::UNCOMPRESSED, &mut ctx)
                .unwrap()
        })
    });
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
