//! ECDSA over P-256: deterministic signatures with HMAC-SHA-256
//! (`vg_ecdsa_p256_sha256_sign`, which calls `vg_ecdsa_p256_sign`), and
//! public keys (`vg_ec_p256_public_key`).

#![cfg(target_arch = "x86_64")]

use super::{Curve, Error, SigningKey, sealed};
use crate::arch::ec_p256::vg_ec_p256_public_key;
use crate::arch::ecdsa_p256_sha256::{
    vg_ecdsa_p256_sha256_sign, vg_ecdsa_p256_sha256_sign_avx2, vg_ecdsa_p256_sha256_sign_shani,
};
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::zeroize::zeroize;

/// The curve P-256 (FIPS 186-5's secp256r1; SP 800-186 §3.2.1.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P256 {}

impl sealed::Sealed for P256 {}

impl Curve for P256 {
    type PrivateKey = [u8; 32];
}

impl SigningKey<P256> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 32 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 65], Error> {
        let mut out = [0; 65];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 65 bytes, `self.d`
        // for reads of 32 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_p256_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    /// Signs the SHA-256 hash of `message` (RFC 6979 §3.2, with SHA-256 as
    /// the message's hash function and HMAC's): the signature `r ‖ s`,
    /// each 32 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn sign_sha256(&self, message: &[u8]) -> Result<[u8; 64], Error> {
        self.sign_sha256_prehashed(&Sha256::digest(message))
    }

    /// Signs `digest`, the SHA-256 hash of a message, as
    /// [`sign_sha256`](Self::sign_sha256) signs the message.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn sign_sha256_prehashed(&self, digest: &[u8; 32]) -> Result<[u8; 64], Error> {
        let sign = match Sha256Backend::select(crate::cpu::detected()) {
            Sha256Backend::Scalar => vg_ecdsa_p256_sha256_sign,
            Sha256Backend::ShaNi => vg_ecdsa_p256_sha256_sign_shani,
            Sha256Backend::Avx2 => vg_ecdsa_p256_sha256_sign_avx2,
        };
        let mut out = [0; 64];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 64 bytes, `self.d`
        // and `digest` for reads of 32 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-256 selected
        // for this CPU does not.
        let ok = unsafe { sign(&mut out, &self.d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}
