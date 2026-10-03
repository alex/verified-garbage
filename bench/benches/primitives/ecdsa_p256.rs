//! ECDSA over P-256 with SHA-256 beside OpenSSL.

use criterion::Criterion;

pub const USES: &[&str] = &["ecdsa_p256_sha256", "ecdsa_p256", "hmac_sha256", "sha256"];

/// Signing a message with SHA-256: deterministically (RFC 6979), and in
/// OpenSSL with a random `k` (its default).
#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::ec::{EcGroup, EcKey, EcPoint};
    use openssl::hash::MessageDigest;
    use openssl::nid::Nid;
    use openssl::pkey::PKey;
    use openssl::sign::Signer;
    use verified_garbage::ecdsa::{P256, SigningKey};

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
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
