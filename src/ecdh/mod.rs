//! Elliptic curve Diffie-Hellman: the ECC CDH primitive of NIST SP 800-56A
//! Rev. 3, §5.7.1.2.
//!
//! A [`PrivateKey<C>`] holds a private key on the curve `C` (so far
//! [`P256`], the curves of [`ecdsa`](crate::ecdsa)). Each exchange is one
//! call of verified code (`vg_ecdh_<curve>`, contract
//! `VG.Spec.Ecdh.Instance.exchangeContract`): it validates the peer's public
//! key as SP 800-56A §5.6.2.3.3 requires (the uncompressed form of SEC 1
//! §2.3.3, both coordinates below `p`, on the curve), checks the private
//! key, and returns the x-coordinate of `dQ`, in constant time. The public
//! key is one call too (`vg_ec_<curve>_public_key`).

#![cfg(target_arch = "x86_64")]

mod p256;

pub use crate::ecdsa::{Curve, P256};

use crate::zeroize::zeroize;

/// Why an operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The private key is not in `[1, n − 1]`, or (for an exchange) the
    /// peer's public key is not a valid uncompressed public key on the
    /// curve. The verified code does not say which.
    InvalidKey,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::InvalidKey => "invalid ECDH key",
        })
    }
}

impl core::error::Error for Error {}

/// An ECDH private key on the curve `C`.
///
/// The key is cleared when it is dropped. Debug output omits it.
pub struct PrivateKey<C: Curve> {
    d: C::PrivateKey,
}

impl<C: Curve> PrivateKey<C> {
    /// Imports a private key `d`, most significant byte first. Each
    /// operation checks that it is in `[1, n − 1]`.
    pub fn from_bytes(d: &C::PrivateKey) -> Self {
        Self { d: d.clone() }
    }
}

impl<C: Curve> Clone for PrivateKey<C> {
    fn clone(&self) -> Self {
        Self { d: self.d.clone() }
    }
}

impl<C: Curve> core::fmt::Debug for PrivateKey<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PrivateKey").finish_non_exhaustive()
    }
}

impl<C: Curve> Drop for PrivateKey<C> {
    fn drop(&mut self) {
        zeroize(self.d.as_mut());
    }
}
