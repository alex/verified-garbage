//! Ed25519 (RFC 8032), deterministic signatures from 32-byte seeds.
//!
//! On x86-64, x86, and AArch64, key derivation, signing, and verification each call
//! one complete verified assembly operation, including SHA-512. x86-64 and AArch64
//! variants follow the selected SHA-512 backend. ARMv7 composes
//! verified scalar and group primitives with the SHA-512 API in Rust. Secret
//! scratch values are cleared after use.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::ed25519::{
    vg_ed25519_public_key_avx2, vg_ed25519_public_key_shani,
    vg_ed25519_sign_cached_avx2, vg_ed25519_sign_cached_shani,
    vg_ed25519_verify_avx2, vg_ed25519_verify_shani,
};
#[cfg(any(target_arch = "x86_64", target_arch = "x86", target_arch = "aarch64"))]
use crate::arch::ed25519::{vg_ed25519_public_key, vg_ed25519_sign_cached, vg_ed25519_verify};
#[cfg(target_arch = "aarch64")]
use crate::arch::ed25519::{
    vg_ed25519_public_key_sha3, vg_ed25519_sign_cached_sha3, vg_ed25519_verify_sha3,
};
#[cfg(target_arch = "arm")]
use crate::arch::ed25519::{
    vg_ed25519_scalar_mul_add, vg_ed25519_scalar_reduce, vg_ed25519_verify_equation,
};
#[cfg(target_arch = "arm")]
use crate::hashes::sha512::Sha512;
#[cfg(any(target_arch = "x86_64", target_arch = "x86", target_arch = "aarch64"))]
use crate::hashes::sha512::Sha512Backend;
use crate::zeroize::zeroize;

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
    /// the uncofactored equation. On x86-64, x86, and AArch64 the SHA-512 challenge is
    /// reduced modulo the subgroup order, following RFC 8032 §6; the other targets
    /// currently use the full digest. No additional subgroup or small-order
    /// rejection policy is imposed.
    /// Verification timing may depend on the public key, message, and signature.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        let signature: &[u8; 64] = signature.try_into().map_err(|_| Error::InvalidSignature)?;
        let valid = verify_message(&self.bytes, message, signature);
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
        Self {
            seed: *seed,
            public: VerifyingKey {
                bytes: public_key(seed),
            },
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
        sign_message(&self.seed, &self.public.bytes, message)
    }
}

/// The public key of `seed` (RFC 8032 §5.1.5), with the verified
/// `vg_ed25519_public_key` including SHA-512.
#[cfg(any(target_arch = "x86_64", target_arch = "x86", target_arch = "aarch64"))]
fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    let derive = match Sha512Backend::select(crate::cpu::detected()) {
        Sha512Backend::Scalar => vg_ed25519_public_key,
        #[cfg(target_arch = "x86_64")]
        Sha512Backend::ShaNi => vg_ed25519_public_key_shani,
        #[cfg(target_arch = "x86_64")]
        Sha512Backend::Avx2 => vg_ed25519_public_key_avx2,
        #[cfg(target_arch = "aarch64")]
        Sha512Backend::Sha3 => vg_ed25519_public_key_sha3,
    };
    let mut public = [0u8; 32];
    let mut scratch = [0u64; 1024];
    // SAFETY: the output, seed, and scratch are distinct objects valid for
    // 32, 32, and 8192 bytes, respectively, so they overlap neither each
    // other nor the call's stack, and none wraps the address space. The
    // seed is the caller's. SHA-512's backend selects every required CPU feature.
    unsafe { derive(&mut public, seed, &mut scratch) };
    zeroize(&mut scratch);
    public
}

/// The public key of `seed` (RFC 8032 §5.1.5): SHA-512, pruning, and the
/// verified base-point multiplication.
#[cfg(target_arch = "arm")]
fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    let mut expanded = Sha512::digest(seed);
    let mut scalar = prune(&expanded);
    let mut scratch = [0u64; 1024];
    let public = scalar_base(&scalar, &mut scratch);
    zeroize(&mut scratch);
    zeroize(&mut scalar);
    zeroize(&mut expanded);
    public
}

#[cfg(any(target_arch = "x86_64", target_arch = "x86", target_arch = "aarch64"))]
fn verify_message(pk: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> u32 {
    let verify = match Sha512Backend::select(crate::cpu::detected()) {
        Sha512Backend::Scalar => vg_ed25519_verify,
        #[cfg(target_arch = "x86_64")]
        Sha512Backend::ShaNi => vg_ed25519_verify_shani,
        #[cfg(target_arch = "x86_64")]
        Sha512Backend::Avx2 => vg_ed25519_verify_avx2,
        #[cfg(target_arch = "aarch64")]
        Sha512Backend::Sha3 => vg_ed25519_verify_sha3,
    };
    let mut scratch = [0u64; 1024];
    // SAFETY: input references are valid for their declared lengths and scratch
    // is a distinct writable object. No object overlaps the call stack, and
    // SHA-512's backend selects every required CPU feature.
    let valid = unsafe { verify(pk, message.as_ptr(), message.len(), signature, &mut scratch) };
    zeroize(&mut scratch);
    valid
}

#[cfg(target_arch = "arm")]
fn verify_message(pk: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> u32 {
    let mut hash = Sha512::new();
    hash.update(&signature[..32]);
    hash.update(pk);
    hash.update(message);
    let challenge = hash.finalize();
    let mut scratch = [0u64; 1024];
    // SAFETY: the input arrays are live for their declared sizes, and
    // scratch is a distinct writable object. None wraps the address space.
    let valid = unsafe { vg_ed25519_verify_equation(pk, signature, &challenge, &mut scratch) };
    zeroize(&mut scratch);
    valid
}

#[cfg(target_arch = "arm")]
fn prune(expanded: &[u8; 64]) -> [u8; 32] {
    let mut scalar = [0u8; 32];
    scalar.copy_from_slice(&expanded[..32]);
    scalar[0] &= 248;
    scalar[31] &= 63;
    scalar[31] |= 64;
    scalar
}

#[cfg(target_arch = "arm")]
fn scalar_base(scalar: &[u8; 32], scratch: &mut [u64; 1024]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // SAFETY: output, scalar, and scratch are distinct live objects of the
    // required sizes, without address-space wrapping.
    unsafe { vg_ed25519_scalar_base(&mut out, scalar, scratch) };
    out
}

#[cfg(target_arch = "arm")]
fn reduce(wide: &[u8; 64], scratch: &mut [u64; 1024]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // SAFETY: the output, wide scalar, and scratch are distinct objects valid
    // for 32, 64, and 8192 bytes, respectively, without address-space wrapping.
    unsafe { vg_ed25519_scalar_reduce(&mut out, wide, scratch) };
    out
}

#[cfg(any(target_arch = "x86_64", target_arch = "x86", target_arch = "aarch64"))]
fn sign_message(seed: &[u8; 32], pk: &[u8; 32], message: &[u8]) -> [u8; 64] {
    let sign = match Sha512Backend::select(crate::cpu::detected()) {
        Sha512Backend::Scalar => vg_ed25519_sign_cached,
        #[cfg(target_arch = "x86_64")]
        Sha512Backend::ShaNi => vg_ed25519_sign_cached_shani,
        #[cfg(target_arch = "x86_64")]
        Sha512Backend::Avx2 => vg_ed25519_sign_cached_avx2,
        #[cfg(target_arch = "aarch64")]
        Sha512Backend::Sha3 => vg_ed25519_sign_cached_sha3,
    };
    let mut signature = [0u8; 64];
    let mut scratch = [0u64; 1024];
    // SAFETY: the input references are valid for their declared lengths.
    // Signature and scratch are distinct writable objects, disjoint from the
    // inputs and the call's stack. None wraps the address space. SigningKey's
    // constructor derives pk from this seed, and both fields remain private.
    // SHA-512's backend selects every required CPU feature.
    unsafe {
        sign(
            &mut signature,
            seed,
            pk,
            message.as_ptr(),
            message.len(),
            &mut scratch,
        )
    };
    zeroize(&mut scratch);
    signature
}

#[cfg(target_arch = "arm")]
fn sign_message(seed: &[u8; 32], pk: &[u8; 32], message: &[u8]) -> [u8; 64] {
    let mut expanded = Sha512::digest(seed);
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
    challenge_hash.update(pk);
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

#[cfg(all(test, target_arch = "aarch64"))]
mod tests {
    use super::Sha512Backend;
    use crate::arch::ed25519::{
        VG_ED25519_PUBLIC_KEY_SHA3_FEATURES, VG_ED25519_SIGN_CACHED_SHA3_FEATURES,
        VG_ED25519_VERIFY_SHA3_FEATURES,
    };
    use crate::cpu::{Features, NAMES};

    /// Every feature set selecting SHA-512's optimized backend also supports
    /// each complete Ed25519 operation that uses that backend.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let features = Features(bits);
            match Sha512Backend::select(features) {
                Sha512Backend::Scalar => {}
                Sha512Backend::Sha3 => {
                    assert!(features.contains(Features::all(&[
                        VG_ED25519_PUBLIC_KEY_SHA3_FEATURES,
                        VG_ED25519_SIGN_CACHED_SHA3_FEATURES,
                        VG_ED25519_VERIFY_SHA3_FEATURES,
                    ])));
                }
            }
        }
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod x86_64_tests {
    use super::*;
    use crate::arch::ed25519::{
        VG_ED25519_PUBLIC_KEY_AVX2_FEATURES, VG_ED25519_PUBLIC_KEY_SHANI_FEATURES,
        VG_ED25519_SIGN_CACHED_AVX2_FEATURES, VG_ED25519_SIGN_CACHED_SHANI_FEATURES,
        VG_ED25519_VERIFY_AVX2_FEATURES, VG_ED25519_VERIFY_SHANI_FEATURES,
    };
    use crate::cpu::{Features, NAMES};

    /// Each complete Ed25519 operation needs no CPU feature that
    /// SHA-512's backend is not selected for: on every set of features that
    /// selects it.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            match Sha512Backend::select(f) {
                Sha512Backend::Scalar => {}
                Sha512Backend::ShaNi => {
                    assert!(f.contains(Features::all(&[
                        VG_ED25519_PUBLIC_KEY_SHANI_FEATURES,
                        VG_ED25519_SIGN_CACHED_SHANI_FEATURES,
                        VG_ED25519_VERIFY_SHANI_FEATURES
                    ])))
                }
                Sha512Backend::Avx2 => {
                    assert!(f.contains(Features::all(&[
                        VG_ED25519_PUBLIC_KEY_AVX2_FEATURES,
                        VG_ED25519_SIGN_CACHED_AVX2_FEATURES,
                        VG_ED25519_VERIFY_AVX2_FEATURES
                    ])))
                }
            }
        }
    }
}
