//! ECDSA (FIPS 186-5 §6.4) with deterministic signatures (RFC 6979 §3.2).
//!
//! A [`SigningKey<C>`] holds a private key on the curve `C` (so far
//! [`P256`]). Each signature is one call of verified code, for the curve
//! and the hash function it signs with (`vg_ecdsa_<curve>_<hash>_sign`,
//! contract `VG.Spec.Ecdsa.Rfc6979.Instance.signContract`). That code
//! derives the per-message secret number `k` from the key and the hash with
//! HMAC, as RFC 6979 does, and signs with the verified ECDSA of a given `k`
//! (`vg_ecdsa_<curve>_sign`). It checks the key, and tries further
//! candidates for `k` when one is unsuitable. It follows the implementation
//! of the hash function that this CPU runs (e.g. on x86-64,
//! `vg_ecdsa_p256_sha256_sign_shani` with the SHA extensions).
//!
//! Signing is constant time except for the number of candidates for `k`
//! that it tries, almost always one.

#![cfg(target_arch = "x86_64")]

mod p256;

pub use p256::P256;

use crate::zeroize::zeroize;

mod sealed {
    pub trait Sealed {}
}

/// A curve that ECDSA signs over.
pub trait Curve: sealed::Sealed {
    /// The encoding of a private key: the integer `d` in `[1, n − 1]`, most
    /// significant byte first (`[u8; 32]` for P-256).
    type PrivateKey: AsMut<[u8]> + Clone;
}

/// Why signing failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The private key is not in `[1, n − 1]`. For a valid key, signing
    /// fails only if none of the candidates for `k` it tries is suitable:
    /// for P-256, with probability under 2⁻²⁴⁸.
    InvalidKey,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::InvalidKey => "invalid ECDSA private key",
        })
    }
}

impl core::error::Error for Error {}

/// An ECDSA private key on the curve `C`.
///
/// The key is cleared when it is dropped. Debug output omits it.
pub struct SigningKey<C: Curve> {
    d: C::PrivateKey,
}

impl<C: Curve> SigningKey<C> {
    /// Imports a private key `d`, most significant byte first. Signing
    /// checks that it is in `[1, n − 1]`.
    pub fn from_bytes(d: &C::PrivateKey) -> Self {
        Self { d: d.clone() }
    }
}

impl<C: Curve> Clone for SigningKey<C> {
    fn clone(&self) -> Self {
        Self { d: self.d.clone() }
    }
}

impl<C: Curve> core::fmt::Debug for SigningKey<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SigningKey").finish_non_exhaustive()
    }
}

impl<C: Curve> Drop for SigningKey<C> {
    fn drop(&mut self) {
        zeroize(self.d.as_mut());
    }
}
