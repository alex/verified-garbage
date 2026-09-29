//! PBKDF2-HMAC-SHA-256 (RFC 8018 §5.2).
//!
//! For each block `Tᵢ` of the derived key, `U₁ = HMAC (P, S ‖ INT (i))` is
//! the verified HMAC-SHA-256 ([`Hmac`]), and the rest of the chain,
//! `Uⱼ₊₁ = HMAC (P, Uⱼ)` exclusive-or'ed into `Tᵢ = U₁ ⊕ … ⊕ U_c`, is the
//! verified `vg_pbkdf2_hmac_sha256_iterate` (contract
//! `VG.Spec.Pbkdf2.iterateSha256Contract`), from the streaming states that
//! the HMAC computation starts from (see `super`, which splits the derived
//! key into blocks).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use core::num::NonZeroU32;

use crate::arch::pbkdf2_sha256::vg_pbkdf2_hmac_sha256_iterate;
use crate::hashes::sha256::Sha256;
use crate::hmac::Hmac;

impl super::Pbkdf2Hash for Sha256 {
    type Key = [u8; 192];

    fn pbkdf2_key(prf: &Hmac<Self>) -> [u8; 192] {
        prf.sha256_key_states()
    }

    fn pbkdf2_iterate(key: &[u8; 192], u: &[u8; 32], n: u32, t: &mut [u8; 32]) {
        let mut scratch = [0u64; 48];
        // SAFETY: `key` is valid for reads of 192 bytes, `u` for reads of 32
        // bytes, `t` for reads and writes of 32 bytes and `scratch` for reads
        // and writes of 384 bytes; `t` and `scratch` are distinct objects
        // from each other and the others (`key` and `u` are only read), so
        // they do not overlap each other, the stack arguments (on ARMv7) or
        // (on x86-64) the return address and the stack below it, nor wrap
        // around the address space. `key` holds the streaming states for
        // `K₀ ⊕ ipad` and `K₀ ⊕ opad` that `vg_hmac_sha256_init` left.
        unsafe { vg_pbkdf2_hmac_sha256_iterate(key, u, n, t, &mut scratch) };
    }
}

/// Fills `out` with the key derived from `password` and `salt` with
/// `iterations` iterations of PBKDF2 with HMAC-SHA-256
/// (`pbkdf2_hmac::<Sha256>`).
///
/// # Panics
///
/// If `out` is longer than (2³² − 1) · 32 bytes ("derived key too long" in
/// RFC 8018).
pub fn pbkdf2_hmac_sha256(password: &[u8], salt: &[u8], iterations: NonZeroU32, out: &mut [u8]) {
    super::pbkdf2_hmac::<Sha256>(password, salt, iterations, out);
}
