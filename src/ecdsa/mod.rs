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
//!
//! `public_key` derives a key's public key `Q = dG`, by one call of
//! verified code (`vg_ec_<curve>_public_key`, contract
//! `VG.Spec.EcKey.Instance.publicKeyContract`), in constant time.
//!
//! A [`VerifyingKey<C>`] holds a public key, and checks a signature by one
//! call of verified code (`vg_ecdsa_<curve>_verify`, contract
//! `VG.Spec.Ecdsa.Instance.verifyContract`), which also checks that the key
//! is valid (SP 800-56A §5.6.2.3.3). It runs in constant time, although
//! nothing it handles is secret.

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
    /// The encoding of a public key: the uncompressed form of SEC 1 §2.3.3,
    /// `04 ‖ x ‖ y`, each coordinate most significant byte first
    /// (`[u8; 65]` for P-256).
    type PublicKey: Clone + core::fmt::Debug + PartialEq + Eq;
}

/// Why signing, deriving the public key, or verifying a signature failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The private key is not in `[1, n − 1]`. For a valid key, signing
    /// fails only if none of the candidates for `k` it tries is suitable:
    /// for P-256, with probability under 2⁻²⁴⁸; deriving the public key
    /// never fails.
    InvalidKey,
    /// The signature is not valid for the public key, or the public key is
    /// not valid.
    InvalidSignature,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::InvalidKey => "invalid ECDSA private key",
            Error::InvalidSignature => "invalid ECDSA signature",
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
    /// Imports a private key `d`, most significant byte first. Signing and
    /// deriving the public key check that it is in `[1, n − 1]`.
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

/// An ECDSA public key on the curve `C`, for verifying signatures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyingKey<C: Curve> {
    q: C::PublicKey,
}

impl<C: Curve> VerifyingKey<C> {
    /// Imports a public key, in the uncompressed form of SEC 1 §2.3.3.
    /// Verifying checks that it is valid: a key that is not is never
    /// accepted.
    pub fn from_bytes(q: &C::PublicKey) -> Self {
        Self { q: q.clone() }
    }

    /// The public key, as [`from_bytes`](Self::from_bytes) takes it.
    pub fn to_bytes(&self) -> C::PublicKey {
        self.q.clone()
    }
}
