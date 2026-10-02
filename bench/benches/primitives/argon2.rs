//! Complete Argon2 derivations, including allocation and initialization,
//! and checks of a password against a derived key (`verify`, and
//! `verify_keyed` for Argon2id with a secret and associated data; OpenSSL
//! derives the key and compares it with `CRYPTO_memcmp`).
//!
//! OpenSSL supplies Argon2 from version 3.2; the runners use 3.0. Enable
//! `openssl-argon2` on a supported host to benchmark it alongside this library.

use criterion::Criterion;

pub const USES: &[&str] = &["argon2", "blake2b"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use verified_garbage::argon2::{Params, Variant, derive, derive_keyed, verify, verify_keyed};

    use crate::VG;
    for (variant, name) in [
        (Variant::Argon2d, "argon2d"),
        (Variant::Argon2i, "argon2i"),
        (Variant::Argon2id, "argon2id"),
    ] {
        let mut g = c.benchmark_group(name);
        g.sample_size(10);
        for memory in [1024u32, 16384] {
            let mut out = [0u8; 32];
            g.bench_function(BenchmarkId::new(VG, memory), |b| {
                b.iter(|| {
                    derive(
                        &Params {
                            variant,
                            iterations: 3,
                            memory_kib: memory,
                            lanes: 1,
                        },
                        black_box(b"password"),
                        black_box(b"saltsalt"),
                        usize::MAX,
                        &mut out,
                    )
                    .unwrap()
                })
            });
            #[cfg(feature = "openssl-argon2")]
            {
                let openssl = match variant {
                    Variant::Argon2d => openssl::kdf::argon2d,
                    Variant::Argon2i => openssl::kdf::argon2i,
                    Variant::Argon2id => openssl::kdf::argon2id,
                };
                g.bench_function(BenchmarkId::new(crate::OPENSSL, memory), |b| {
                    b.iter(|| {
                        openssl(
                            None,
                            black_box(b"password"),
                            black_box(b"saltsalt"),
                            None,
                            None,
                            3,
                            1,
                            memory,
                            &mut out,
                        )
                        .unwrap()
                    })
                });
            }
        }
        g.finish();

        let mut g = c.benchmark_group(format!("{name}-verify"));
        g.sample_size(10);
        for memory in [1024u32, 16384] {
            let params = Params {
                variant,
                iterations: 3,
                memory_kib: memory,
                lanes: 1,
            };
            let mut expected = [0u8; 32];
            derive(&params, b"password", b"saltsalt", usize::MAX, &mut expected).unwrap();
            g.bench_function(BenchmarkId::new(VG, memory), |b| {
                b.iter(|| {
                    verify(
                        &params,
                        black_box(b"password"),
                        black_box(b"saltsalt"),
                        usize::MAX,
                        black_box(&expected),
                    )
                    .unwrap()
                })
            });
            #[cfg(feature = "openssl-argon2")]
            {
                let oracle = match variant {
                    Variant::Argon2d => openssl::kdf::argon2d,
                    Variant::Argon2i => openssl::kdf::argon2i,
                    Variant::Argon2id => openssl::kdf::argon2id,
                };
                let mut out = [0u8; 32];
                g.bench_function(BenchmarkId::new(crate::OPENSSL, memory), |b| {
                    b.iter(|| {
                        oracle(
                            None,
                            black_box(b"password"),
                            black_box(b"saltsalt"),
                            None,
                            None,
                            3,
                            1,
                            memory,
                            &mut out,
                        )
                        .unwrap();
                        assert!(openssl::memcmp::eq(&out, black_box(&expected)))
                    })
                });
            }
        }
        g.finish();
    }

    let mut g = c.benchmark_group("argon2id-keyed-verify");
    g.sample_size(10);
    for memory in [1024u32, 16384] {
        let params = Params {
            variant: Variant::Argon2id,
            iterations: 3,
            memory_kib: memory,
            lanes: 1,
        };
        let (secret, ad): (&[u8], &[u8]) = (b"secret", b"associated data");
        let mut expected = [0u8; 32];
        derive_keyed(
            &params,
            b"password",
            b"saltsalt",
            secret,
            ad,
            usize::MAX,
            &mut expected,
        )
        .unwrap();
        g.bench_function(BenchmarkId::new(VG, memory), |b| {
            b.iter(|| {
                verify_keyed(
                    &params,
                    black_box(b"password"),
                    black_box(b"saltsalt"),
                    black_box(secret),
                    black_box(ad),
                    usize::MAX,
                    black_box(&expected),
                )
                .unwrap()
            })
        });
        #[cfg(feature = "openssl-argon2")]
        {
            let mut out = [0u8; 32];
            g.bench_function(BenchmarkId::new(crate::OPENSSL, memory), |b| {
                b.iter(|| {
                    openssl::kdf::argon2id(
                        None,
                        black_box(b"password"),
                        black_box(b"saltsalt"),
                        Some(black_box(ad)),
                        Some(black_box(secret)),
                        3,
                        1,
                        memory,
                        &mut out,
                    )
                    .unwrap();
                    assert!(openssl::memcmp::eq(&out, black_box(&expected)))
                })
            });
        }
    }
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
