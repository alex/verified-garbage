//! The RSA public-key operation (RSAEP, without padding).

use criterion::Criterion;

pub const USES: &[&str] = &["rsa"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::BigNum;
    use openssl::rsa::{Padding, Rsa};
    use verified_garbage::rsa::PublicKey;

    use crate::{OPENSSL, VG};
    let mut g = c.benchmark_group("rsa_public");
    // Moduli of 2048, 3072 and 4096 bits with the exponent 65537; the ids'
    // size is the modulus' bytes. Each library loads the key once, outside
    // the measurements, as a verifier holds a public key across operations.
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e) = (key.n().to_vec(), key.e().to_vec());
        let k = n.len();
        let vg_key = PublicKey::new(&n, &e).unwrap();
        let openssl_key = Rsa::from_public_components(
            BigNum::from_slice(&n).unwrap(),
            BigNum::from_slice(&e).unwrap(),
        )
        .unwrap();
        // An input below the modulus.
        let mut input = vec![0x42; k];
        input[0] = 0;
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                black_box(&vg_key)
                    .public_op(black_box(&input), &mut out)
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                black_box(&openssl_key)
                    .public_encrypt(black_box(&input), &mut out, Padding::NONE)
                    .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
