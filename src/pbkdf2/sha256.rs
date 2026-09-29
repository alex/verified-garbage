//! PBKDF2-HMAC-SHA-256 (RFC 8018 §5.2).
//!
//! For each block `Tᵢ` of the derived key, `U₁ = HMAC (P, S ‖ INT (i))` is
//! the verified HMAC-SHA-256 ([`Hmac`]), and the rest of the chain,
//! `Uⱼ₊₁ = HMAC (P, Uⱼ)` exclusive-or'ed into `Tᵢ = U₁ ⊕ … ⊕ U_c`, is the
//! verified `vg_pbkdf2_hmac_sha256_iterate` (contract
//! `VG.Spec.Pbkdf2.iterateSha256Contract`), from the streaming states that
//! the HMAC computation starts from (see `super`, which splits the derived
//! key into blocks).
//!
//! On x86-64, when the HMAC computation runs SHA-256 with the SHA extensions,
//! the iteration does too: `vg_pbkdf2_hmac_sha256_iterate_shani`, the same
//! verified code calling `vg_sha256_compress_shani`, with the same contract.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use core::num::NonZeroU32;

use crate::arch::pbkdf2_sha256::vg_pbkdf2_hmac_sha256_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha256::vg_pbkdf2_hmac_sha256_iterate_shani;
use crate::hashes::sha256::Sha256;
#[cfg(target_arch = "x86_64")]
use crate::hashes::sha256::Sha256Backend;
use crate::hmac::Hmac;

/// The streaming states for `K₀ ⊕ ipad` and `K₀ ⊕ opad`, and (on x86-64) the
/// implementation of SHA-256 the HMAC computation runs.
#[doc(hidden)]
pub struct Key {
    states: [u8; 192],
    #[cfg(target_arch = "x86_64")]
    backend: Sha256Backend,
}

impl super::Pbkdf2Hash for Sha256 {
    type Key = Key;

    fn pbkdf2_key(prf: &Hmac<Self>) -> Key {
        Key {
            states: prf.sha256_key_states(),
            #[cfg(target_arch = "x86_64")]
            backend: prf.sha256_backend(),
        }
    }

    fn pbkdf2_iterate(key: &Key, u: &[u8; 32], n: u32, t: &mut [u8; 32]) {
        #[cfg(target_arch = "x86_64")]
        let iterate = match key.backend {
            Sha256Backend::Scalar => vg_pbkdf2_hmac_sha256_iterate,
            Sha256Backend::ShaNi => vg_pbkdf2_hmac_sha256_iterate_shani,
        };
        #[cfg(not(target_arch = "x86_64"))]
        let iterate = vg_pbkdf2_hmac_sha256_iterate;
        let mut scratch = [0u64; 104];
        // SAFETY: `key.states` is valid for reads of 192 bytes, `u` for reads
        // of 32 bytes, `t` for reads and writes of 32 bytes and `scratch` for
        // reads and writes of 832 bytes; `t` and `scratch` are distinct
        // objects from each other and the others (`key` and `u` are only
        // read), so they do not overlap each other, the stack arguments (on
        // ARMv7) or (on x86-64) the return address and the stack below it,
        // nor wrap around the address space. `key.states` holds the
        // streaming states for `K₀ ⊕ ipad` and `K₀ ⊕ opad` that
        // `vg_hmac_sha256_init` left. On x86-64, `iterate` needs the CPU
        // features of the SHA-256 implementation the HMAC computation was
        // created with, which were detected (`tests::shani_features`).
        unsafe { iterate(&key.states, u, n, t, &mut scratch) };
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

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use crate::arch::pbkdf2_sha256::VG_PBKDF2_HMAC_SHA256_ITERATE_SHANI_FEATURES;
    use crate::arch::sha256::{VG_SHA256_FINALIZE_SHANI_FEATURES, VG_SHA256_UPDATE_SHANI_FEATURES};
    use crate::cpu::Features;

    /// The SHA-NI iteration needs no CPU feature that the SHA-NI SHA-256
    /// backend was not selected for.
    #[test]
    fn shani_features() {
        let backend = Features::all(&[
            VG_SHA256_UPDATE_SHANI_FEATURES,
            VG_SHA256_FINALIZE_SHANI_FEATURES,
        ]);
        assert!(backend.contains(Features::of(VG_PBKDF2_HMAC_SHA256_ITERATE_SHANI_FEATURES)));
    }
}
