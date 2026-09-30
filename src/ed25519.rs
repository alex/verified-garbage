//! Ed25519 (RFC 8032), deterministic signatures from 32-byte seeds.
//!
//! SHA-512 uses the hash API's selected backend. Scalar reduction,
//! multiply-add, and point multiplication use verified assembly with the
//! contracts in `VG.Spec.Ed25519`. Rust composes those primitives and clears
//! secret temporary values.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86"))]

use crate::arch::ed25519::{
    vg_ed25519_scalar_base, vg_ed25519_scalar_mul_add, vg_ed25519_scalar_reduce,
    vg_ed25519_verify_equation,
};
use crate::hashes::sha512::Sha512;
use crate::mlkem768::zeroize;

/// Why signature verification failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The signature has the wrong length, a noncanonical encoding, or an invalid equation.
    InvalidSignature,
}

/// An encoded Ed25519 public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    bytes: [u8; 32],
}

impl VerifyingKey {
    /// Import an encoded public key. Its encoding is checked during verification.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        Self { bytes: *bytes }
    }

    /// The encoded public key.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// Verify a pure Ed25519 signature (RFC 8032 §5.1.7).
    ///
    /// Public keys and signatures must use canonical encodings, and the
    /// signature scalar must be less than the subgroup order. This checks
    /// the uncofactored equation using the full SHA-512 challenge. It does
    /// not impose an additional subgroup or small-order rejection policy.
    /// Verification timing may depend on the public key, message, and signature.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        let signature: &[u8; 64] = signature.try_into().map_err(|_| Error::InvalidSignature)?;
        let mut hash = Sha512::new();
        hash.update(&signature[..32]);
        hash.update(&self.bytes);
        hash.update(message);
        let challenge = hash.finalize();
        let mut scratch = [0u64; 1024];
        // SAFETY: the input arrays are live for their declared sizes, and
        // scratch is a distinct writable object. None wraps the address space.
        let valid =
            unsafe { vg_ed25519_verify_equation(&self.bytes, signature, &challenge, &mut scratch) };
        zeroize(&mut scratch);
        if valid == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

/// An Ed25519 signing key, storing its seed and derived public key.
///
/// The seed is cleared when the key is dropped. Debug output omits it.
#[derive(Clone)]
pub struct SigningKey {
    seed: [u8; 32],
    public: VerifyingKey,
}

impl core::fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SigningKey").finish_non_exhaustive()
    }
}

impl Drop for SigningKey {
    fn drop(&mut self) {
        zeroize(&mut self.seed);
    }
}

impl SigningKey {
    /// Derive a signing key and its public key from an RFC 8032 seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let mut expanded = Sha512::digest(seed);
        let mut scalar = prune(&expanded);
        let mut scratch = [0u64; 1024];
        let public = VerifyingKey {
            bytes: scalar_base(&scalar, &mut scratch),
        };
        zeroize(&mut scratch);
        zeroize(&mut scalar);
        zeroize(&mut expanded);
        Self {
            seed: *seed,
            public,
        }
    }

    /// The original 32-byte seed.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// The public key derived from this key's seed.
    pub fn verifying_key(&self) -> &VerifyingKey {
        &self.public
    }

    /// Sign `message` deterministically using pure Ed25519 (RFC 8032 §5.1.6).
    pub fn sign(&self, message: &[u8]) -> [u8; 64] {
        let mut expanded = Sha512::digest(&self.seed);
        let mut scalar = prune(&expanded);
        let mut nonce_hash = Sha512::new();
        nonce_hash.update(&expanded[32..]);
        nonce_hash.update(message);
        let mut nonce_digest = nonce_hash.finalize();
        let mut scratch = [0u64; 1024];
        let mut nonce = reduce(&nonce_digest, &mut scratch);
        let r = scalar_base(&nonce, &mut scratch);
        let mut challenge_hash = Sha512::new();
        challenge_hash.update(&r);
        challenge_hash.update(&self.public.bytes);
        challenge_hash.update(message);
        let mut challenge_digest = challenge_hash.finalize();
        let mut challenge = reduce(&challenge_digest, &mut scratch);
        let mut s = [0u8; 32];
        // SAFETY: the output, inputs, and scratch are distinct live objects
        // of the required sizes, with no overlap or address-space wrapping.
        unsafe { vg_ed25519_scalar_mul_add(&mut s, &nonce, &challenge, &scalar, &mut scratch) };
        let mut signature = [0u8; 64];
        signature[..32].copy_from_slice(&r);
        signature[32..].copy_from_slice(&s);
        zeroize(&mut scratch);
        zeroize(&mut expanded);
        zeroize(&mut scalar);
        zeroize(&mut nonce_digest);
        zeroize(&mut nonce);
        zeroize(&mut challenge_digest);
        zeroize(&mut challenge);
        zeroize(&mut s);
        signature
    }
}

fn prune(expanded: &[u8; 64]) -> [u8; 32] {
    let mut scalar = [0u8; 32];
    scalar.copy_from_slice(&expanded[..32]);
    scalar[0] &= 248;
    scalar[31] &= 63;
    scalar[31] |= 64;
    scalar
}

fn scalar_base(scalar: &[u8; 32], scratch: &mut [u64; 1024]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // SAFETY: the output, scalar, and scratch are distinct objects valid
    // for 32, 32, and 8192 bytes, respectively, without address-space wrapping.
    unsafe { vg_ed25519_scalar_base(&mut out, scalar, scratch) };
    out
}

fn reduce(wide: &[u8; 64], scratch: &mut [u64; 1024]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // SAFETY: the output, wide scalar, and scratch are distinct objects valid
    // for 32, 64, and 8192 bytes, respectively, without address-space wrapping.
    unsafe { vg_ed25519_scalar_reduce(&mut out, wide, scratch) };
    out
}
