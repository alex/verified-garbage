//! PBKDF2-HMAC-SHA-256 (RFC 8018 §5.2).
//!
//! For each block `Tᵢ` of the derived key, `U₁ = HMAC (P, S ‖ INT (i))` is
//! the verified HMAC-SHA-256 ([`Hmac`]), and the rest of the chain,
//! `Uⱼ₊₁ = HMAC (P, Uⱼ)` exclusive-or'ed into `Tᵢ = U₁ ⊕ … ⊕ U_c`, is the
//! verified `vg_pbkdf2_hmac_sha256_iterate` (contract
//! `VG.Spec.Pbkdf2.iterateSha256Contract`), from the streaming states that
//! the HMAC computation starts from. This module only splits the derived key
//! into blocks and truncates the last one.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use core::num::NonZeroU32;

#[cfg(target_arch = "aarch64")]
use crate::asm::aarch64::pbkdf2_sha256::vg_pbkdf2_hmac_sha256_iterate;
#[cfg(target_arch = "arm")]
use crate::asm::arm::pbkdf2_sha256::vg_pbkdf2_hmac_sha256_iterate;
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::pbkdf2_sha256::vg_pbkdf2_hmac_sha256_iterate;
use crate::hashes::sha256::Sha256;
use crate::hmac::Hmac;

/// Fills `out` with the key derived from `password` and `salt` with
/// `iterations` iterations of PBKDF2 with HMAC-SHA-256.
///
/// # Panics
///
/// If `out` is longer than (2³² − 1) · 32 bytes ("derived key too long" in
/// RFC 8018).
pub fn pbkdf2_hmac_sha256(password: &[u8], salt: &[u8], iterations: NonZeroU32, out: &mut [u8]) {
    let prf = Hmac::<Sha256>::new(password);
    let key = prf.sha256_key_states();
    let mut scratch = [0u64; 48];
    for (i, block) in out.chunks_mut(32).enumerate() {
        let index = u32::try_from(i + 1).expect("PBKDF2 derived key too long");
        let mut mac = prf.clone();
        mac.update(salt);
        mac.update(&index.to_be_bytes());
        let u = mac.finalize();
        let mut t = u;
        // SAFETY: `key` is valid for reads of 192 bytes, `u` for reads of 32
        // bytes, `t` for reads and writes of 32 bytes and `scratch` for reads
        // and writes of 384 bytes; they are distinct objects, so they do not
        // overlap each other, the stack arguments (on ARMv7) or (on x86-64) the return address and the stack
        // below it. `key` holds the streaming states for `K₀ ⊕ ipad` and
        // `K₀ ⊕ opad` that `vg_hmac_sha256_init` left, so `t` becomes
        // `U₁ ⊕ U₂ ⊕ … ⊕ U_c`.
        unsafe {
            vg_pbkdf2_hmac_sha256_iterate(&key, &u, iterations.get() - 1, &mut t, &mut scratch)
        };
        block.copy_from_slice(&t[..block.len()]);
    }
}
