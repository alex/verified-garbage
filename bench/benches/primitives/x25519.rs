//! X25519.

use criterion::Criterion;

/// The library modules whose code these benchmarks run (see
/// `ci/bench_arches.py`).
pub const USES: &[&str] = &["x25519"];

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::derive::Deriver;
    use openssl::pkey::{Id, PKey};
    use verified_garbage::x25519::PrivateKey;

    use crate::{OPENSSL, VG};
    let private = [0x42; 32];
    let peer = PrivateKey::from_bytes(&[0x24; 32]).public_key();
    let mut g = c.benchmark_group("x25519");
    // One Diffie-Hellman: a shared secret from a private key and the peer's
    // public key. The ids' size is the bytes of the shared secret.
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| {
            PrivateKey::from_bytes(black_box(&private))
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let key = PKey::private_key_from_raw_bytes(black_box(&private), Id::X25519).unwrap();
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer), Id::X25519).unwrap();
            let mut d = Deriver::new(&key).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
