//! Complete Argon2 derivations, including allocation and initialization.
//!
//! OpenSSL supplies Argon2 from version 3.2; the runners use 3.0. Enable
//! `openssl-argon2` on a supported host to benchmark it alongside this library.

use criterion::Criterion;

pub const USES: &[&str] = &["argon2", "blake2b"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use verified_garbage::argon2::{Variant, derive};

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
                        variant,
                        black_box(b"password"),
                        black_box(b"saltsalt"),
                        3,
                        memory,
                        1,
                        1,
                        b"",
                        b"",
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
    }
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
