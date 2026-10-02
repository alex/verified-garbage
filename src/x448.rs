//! X448 (RFC 7748), Diffie-Hellman on Curve448.
//!
//! The whole function is the verified assembly `vg_x448` (contract
//! `VG.Spec.X448.x448Contract`): `X448(k, u)` of RFC 7748 §5, the
//! scalar decoded (clamped) and all 448 bits of the u-coordinate reduced
//! modulo the field prime, in constant time. This module gives it working
//! space, and destroys what it leaves there.
//!
//! [`diffie_hellman`](PrivateKey::diffie_hellman) rejects the all-zero
//! shared secret that a public key of small order gives (RFC 7748 §6.2), in
//! constant time; [`x448`] is the function itself, which does not.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use crate::arch::x448::vg_x448;
use crate::zeroize::zeroize;

/// Why an operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The shared secret is all zero: the peer's public key is a point of
    /// small order (RFC 7748 §6.2).
    ZeroSharedSecret,
    /// The operating system's random number generator failed.
    Randomness,
}

/// The u-coordinate of the base point, 5 (RFC 7748 §4.2), encoded.
pub const BASE_POINT: [u8; 56] = {
    let mut b = [0; 56];
    b[0] = 5;
    b
};

/// `X448(scalar, u)` (RFC 7748 §5), which may be all zero.
pub fn x448(scalar: &[u8; 56], u: &[u8; 56]) -> [u8; 56] {
    let mut out = [0u8; 56];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` and `scratch` are valid for reads and writes of 56 and
    // 8192 bytes, and `scalar` and `u` for reads of 56 bytes; the writable
    // buffers are disjoint from each other and from the inputs.
    // No buffer overlaps the callee's stack or wraps around the address space.
    unsafe { vg_x448(&mut out, scalar, u, &mut scratch) };
    zeroize(&mut scratch);
    out
}

/// An X448 private key: 56 bytes, which X448 decodes into a scalar.
#[derive(Clone)]
pub struct PrivateKey {
    bytes: [u8; 56],
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
    pub const SIZE: usize = 56;

    /// A new private key: 56 random bytes from the operating system.
    pub fn generate() -> Result<Self, Error> {
        let mut bytes = [0u8; 56];
        if getrandom::fill(&mut bytes).is_err() {
            // The operating system's generator does not fail in the tests.
            // NO-COVERAGE-START
            return Err(Error::Randomness);
            // NO-COVERAGE-END
        }
        Ok(PrivateKey { bytes })
    }

    /// The private key `bytes`.
    pub fn from_bytes(bytes: &[u8; 56]) -> Self {
        PrivateKey { bytes: *bytes }
    }

    /// The bytes of the key.
    pub fn as_bytes(&self) -> &[u8; 56] {
        &self.bytes
    }

    /// The public key, `X448(k, 5)` (RFC 7748 §6.2).
    pub fn public_key(&self) -> [u8; 56] {
        x448(&self.bytes, &BASE_POINT)
    }

    /// The shared secret with the peer whose public key is `peer`,
    /// `X448(k, peer)` (RFC 7748 §6.2); [`Error::ZeroSharedSecret`] if it
    /// is all zero, which is checked without revealing anything else about
    /// it.
    pub fn diffie_hellman(&self, peer: &[u8; 56]) -> Result<[u8; 56], Error> {
        let mut shared = x448(&self.bytes, peer);
        if crate::ct::eq(&shared, &[0; 56]) {
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

    /// The point 0 has small order: the shared secret is zero.
    #[test]
    fn zero_shared_secret() {
        let a = PrivateKey::from_bytes(&[0x42; 56]);
        assert_eq!(a.diffie_hellman(&[0; 56]), Err(Error::ZeroSharedSecret));
        assert_eq!(x448(a.as_bytes(), &[0; 56]), [0; 56]);
    }
}
