//! SHA-3 and SHAKE.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["sha3"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha3::{
        Sha3_224, Sha3_256, Sha3_384, Sha3_512, Shake128, Shake256,
    };

    use crate::hash_group;
    hash_group(c, "sha3-224", Sha3_224::digest, MessageDigest::sha3_224());
    hash_group(c, "sha3-256", Sha3_256::digest, MessageDigest::sha3_256());
    hash_group(c, "sha3-384", Sha3_384::digest, MessageDigest::sha3_384());
    hash_group(c, "sha3-512", Sha3_512::digest, MessageDigest::sha3_512());
    xof_group(c, "shake128", Shake128::digest, MessageDigest::shake_128());
    xof_group(c, "shake256", Shake256::digest, MessageDigest::shake_256());
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}

/// Benchmarks the extendable-output function `vg` against OpenSSL's `md`,
/// with 32 bytes of output.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
fn xof_group(
    c: &mut Criterion,
    name: &str,
    vg: fn(&[u8], &mut [u8]),
    md: openssl::hash::MessageDigest,
) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::hash::Hasher;

    use crate::{OPENSSL, SIZES, VG};
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mut out = [0u8; 32];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| vg(black_box(&data), &mut out))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut h = Hasher::new(md).unwrap();
                h.update(black_box(&data)).unwrap();
                h.finish_xof(&mut out).unwrap();
            })
        });
    }
    g.finish();
}
