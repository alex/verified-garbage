//! X25519 (RFC 7748), Diffie-Hellman on Curve25519.
//!
//! The whole function is the verified assembly `vg_x25519` (contract
//! `VG.Spec.X25519.x25519Contract`): `X25519(k, u)` of RFC 7748 §5, the
//! scalar decoded (clamped) and the u-coordinate's top bit masked as the RFC
//! specifies, in constant time. On x86-64 CPUs with BMI2 and ADX it is
//! `vg_x25519_adx`, with the same contract and faster field multiplications,
//! and on those that also have AVX512_IFMA and AVX512VL `vg_x25519_ifma`,
//! whose ladder does four field multiplications at once.
//! This module gives it working space, and destroys what it leaves there.
//!
//! [`diffie_hellman`](PrivateKey::diffie_hellman) rejects the all-zero
//! shared secret that a public key of small order gives (RFC 7748 §6.1), in
//! constant time; [`x25519`] is the function itself, which does not.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]

use crate::arch::x25519::vg_x25519;
#[cfg(target_arch = "x86_64")]
use crate::arch::x25519::{
    VG_X25519_ADX_FEATURES, VG_X25519_IFMA_FEATURES, vg_x25519_adx, vg_x25519_ifma,
};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The implementations of `vg_x25519`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// The target's baseline ISA.
    Baseline,
    /// BMI2's `mulx` and ADX's `adcx` and `adox`.
    #[cfg(target_arch = "x86_64")]
    Adx,
    /// AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq` (on `ymm` registers,
    /// with AVX512VL) for the ladder, and `Adx`'s multiplications for the
    /// inversion.
    #[cfg(target_arch = "x86_64")]
    Ifma,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Backend {
        if f.contains(VG_X25519_IFMA_FEATURES) {
            Backend::Ifma
        } else if f.contains(VG_X25519_ADX_FEATURES) {
            Backend::Adx
        } else {
            Backend::Baseline
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    fn select(_: Features) -> Backend {
        Backend::Baseline
    }
}

/// Why an operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The shared secret is all zero: the peer's public key is a point of
    /// small order (RFC 7748 §6.1).
    ZeroSharedSecret,
    /// The operating system's random number generator failed.
    Randomness,
}

/// The u-coordinate of the base point, 9 (RFC 7748 §4.1), encoded.
pub const BASE_POINT: [u8; 32] = {
    let mut b = [0; 32];
    b[0] = 9;
    b
};

/// `X25519(scalar, u)` (RFC 7748 §5), which may be all zero.
pub fn x25519(scalar: &[u8; 32], u: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut scratch = [0u64; 512];
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_x25519,
        // `select` chose it because the CPU has the features it needs.
        #[cfg(target_arch = "x86_64")]
        Backend::Adx => vg_x25519_adx,
        #[cfg(target_arch = "x86_64")]
        Backend::Ifma => vg_x25519_ifma,
    };
    // SAFETY: `out` and `scratch` are valid for reads and writes of 32 and
    // 4096 bytes, and `scalar` and `u` for reads of 32 bytes; they are
    // distinct Rust objects, so they do not overlap each other or the stack,
    // or wrap around the end of the address space; and the CPU has the
    // features of the function `select` chose.
    unsafe { f(&mut out, scalar, u, &mut scratch) };
    zeroize(&mut scratch);
    out
}

/// An X25519 private key: 32 bytes, which X25519 decodes into a scalar.
#[derive(Clone)]
pub struct PrivateKey {
    bytes: [u8; 32],
}

impl core::fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PrivateKey").finish_non_exhaustive()
    }
}

impl Drop for PrivateKey {
    fn drop(&mut self) {
        zeroize(&mut self.bytes);
    }
}

impl PrivateKey {
    /// The size of a private key, of a public key and of a shared secret, in
    /// bytes.
    pub const SIZE: usize = 32;

    /// A new private key: 32 random bytes from the operating system.
    pub fn generate() -> Result<Self, Error> {
        let mut bytes = [0u8; 32];
        if getrandom::fill(&mut bytes).is_err() {
            // The operating system's generator does not fail in the tests.
            // NO-COVERAGE-START
            return Err(Error::Randomness);
            // NO-COVERAGE-END
        }
        Ok(PrivateKey { bytes })
    }

    /// The private key `bytes`.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        PrivateKey { bytes: *bytes }
    }

    /// The bytes of the key.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// The public key, `X25519(k, 9)` (RFC 7748 §6.1).
    pub fn public_key(&self) -> [u8; 32] {
        x25519(&self.bytes, &BASE_POINT)
    }

    /// The shared secret with the peer whose public key is `peer`,
    /// `X25519(k, peer)` (RFC 7748 §6.1); [`Error::ZeroSharedSecret`] if it
    /// is all zero, which is checked without revealing anything else about
    /// it.
    pub fn diffie_hellman(&self, peer: &[u8; 32]) -> Result<[u8; 32], Error> {
        let mut shared = x25519(&self.bytes, peer);
        if crate::ct::eq(&shared, &[0; 32]) {
            zeroize(&mut shared);
            return Err(Error::ZeroSharedSecret);
        }
        Ok(shared)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A generated key agrees with itself: both sides compute the same
    /// secret.
    #[test]
    fn agreement() {
        let a = PrivateKey::generate().unwrap();
        let b = PrivateKey::generate().unwrap();
        assert_ne!(a.as_bytes(), b.as_bytes());
        let ka = a.public_key();
        let kb = b.public_key();
        assert_eq!(a.diffie_hellman(&kb), b.diffie_hellman(&ka));
        assert_eq!(PrivateKey::from_bytes(a.as_bytes()).public_key(), ka);
        assert_eq!(a.clone().public_key(), ka);
    }

    /// The baseline agrees with the implementation chosen for this CPU,
    /// and the choice follows the features.
    #[test]
    fn backends() {
        let k = [0x42; 32];
        let u = PrivateKey::from_bytes(&[0x24; 32]).public_key();
        let mut out = [0u8; 32];
        let mut scratch = [0u64; 512];
        // SAFETY: as in `x25519`, and the baseline needs no CPU feature.
        unsafe { vg_x25519(&mut out, &k, &u, &mut scratch) };
        assert_eq!(out, x25519(&k, &u));
        assert_eq!(Backend::select(Features(0)), Backend::Baseline);
        #[cfg(target_arch = "x86_64")]
        {
            let adx = VG_X25519_ADX_FEATURES;
            assert_eq!(Backend::select(adx), Backend::Adx);
            assert_eq!(Backend::select(Features::of(&["bmi2"])), Backend::Baseline);
            let ifma = VG_X25519_IFMA_FEATURES;
            assert_eq!(Backend::select(ifma), Backend::Ifma);
            assert_eq!(
                Backend::select(Features(adx.0 | Features::of(&["avx512ifma"]).0)),
                Backend::Adx
            );
        }
    }

    /// The point 0 has small order: the shared secret is zero.
    #[test]
    fn zero_shared_secret() {
        let a = PrivateKey::from_bytes(&[0x42; 32]);
        assert_eq!(a.diffie_hellman(&[0; 32]), Err(Error::ZeroSharedSecret));
        assert_eq!(x25519(a.as_bytes(), &[0; 32]), [0; 32]);
    }
}
