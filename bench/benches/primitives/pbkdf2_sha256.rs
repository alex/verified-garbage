//! PBKDF2-HMAC-SHA-256.

use criterion::Criterion;

pub const USES: &[&str] = &["pbkdf2_sha256", "hmac_sha256", "sha256"];

/// PBKDF2-HMAC-SHA-256 of a 32-byte key (one block), with the sizes as the
/// iteration counts: deriving it, and checking a password against it
/// (`pbkdf2_hmac_verify`, one instance of the generic function; OpenSSL
/// derives the key and compares it with `CRYPTO_memcmp`).
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;
    use std::num::NonZeroU32;

    use criterion::{BenchmarkId, Throughput};
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha256::Sha256;
    use verified_garbage::pbkdf2::{pbkdf2_hmac, pbkdf2_hmac_verify};

    use crate::{OPENSSL, SIZES, VG};

    crate::pbkdf2_group(
        c,
        "pbkdf2-hmac-sha256",
        pbkdf2_hmac::<Sha256>,
        MessageDigest::sha256(),
        32,
    );

    let password = [0x0b; 32];
    let salt = [0x5a; 16];
    let mut g = c.benchmark_group("pbkdf2-hmac-sha256-verify");
    for iterations in SIZES {
        g.throughput(Throughput::Elements(iterations as u64));
        let n = NonZeroU32::new(iterations as u32).unwrap();
        let mut expected = [0u8; 32];
        pbkdf2_hmac::<Sha256>(&password, &salt, n, &mut expected);
        g.bench_function(BenchmarkId::new(VG, iterations), |b| {
            b.iter(|| {
                pbkdf2_hmac_verify::<Sha256>(
                    black_box(&password),
                    black_box(&salt),
                    n,
                    black_box(&expected),
                )
                .unwrap()
            })
        });
        let mut out = [0u8; 32];
        g.bench_function(BenchmarkId::new(OPENSSL, iterations), |b| {
            b.iter(|| {
                openssl::pkcs5::pbkdf2_hmac(
                    black_box(&password),
                    black_box(&salt),
                    iterations,
                    MessageDigest::sha256(),
                    &mut out,
                )
                .unwrap();
                assert!(openssl::memcmp::eq(&out, black_box(&expected)))
            })
        });
    }
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
