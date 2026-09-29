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
//! On x86-64 and AArch64 the whole function is instead one call of the
//! verified `vg_pbkdf2_hmac_sha256` (contract
//! `VG.Spec.Pbkdf2.pbkdf2Sha256Contract`), which composes the verified
//! SHA-256, HMAC-SHA-256 and PBKDF2 functions by calls; on x86-64,
//! `vg_pbkdf2_hmac_sha256_shani` when SHA-256 runs with the SHA extensions
//! on this CPU, the same verified code calling the SHA-NI functions, with
//! the same contract.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use core::num::NonZeroU32;

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use crate::arch::pbkdf2_sha256::vg_pbkdf2_hmac_sha256;
use crate::arch::pbkdf2_sha256::vg_pbkdf2_hmac_sha256_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha256::{
    vg_pbkdf2_hmac_sha256_iterate_shani, vg_pbkdf2_hmac_sha256_shani,
};
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
        let mut scratch = [0u64; 48];
        // SAFETY: `key.states` is valid for reads of 192 bytes, `u` for reads
        // of 32 bytes, `t` for reads and writes of 32 bytes and `scratch` for
        // reads and writes of 384 bytes; `t` and `scratch` are distinct
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

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    fn pbkdf2_derive(password: &[u8], salt: &[u8], iterations: NonZeroU32, out: &mut [u8]) {
        #[cfg(target_arch = "x86_64")]
        let derive = match Sha256Backend::select(crate::cpu::detected()) {
            Sha256Backend::Scalar => vg_pbkdf2_hmac_sha256,
            Sha256Backend::ShaNi => vg_pbkdf2_hmac_sha256_shani,
        };
        #[cfg(target_arch = "aarch64")]
        let derive = vg_pbkdf2_hmac_sha256;
        u32::try_from(out.len().div_ceil(32)).expect("PBKDF2 derived key too long");
        let mut scratch = [0u64; 256];
        // SAFETY: `iterations` is positive and `out` at most (2³² − 1) · 32
        // bytes long (checked above). `password` and `salt` are valid for
        // reads of their lengths, `out` for reads and writes of its length
        // and `scratch` for reads and writes of 2048 bytes; `out` and
        // `scratch` are distinct objects from each other and the others
        // (`password` and `salt` are only read), so none of them overlaps
        // another written one, the stack arguments, the return address or
        // the stack below it, and, as Rust objects, none wraps around the
        // address space. On x86-64, `derive` needs the CPU features of the
        // SHA-256 implementation selected for this CPU, which were detected
        // (`tests::shani_features`).
        unsafe {
            derive(
                password.as_ptr(),
                password.len(),
                salt.as_ptr(),
                salt.len(),
                iterations.get(),
                out.as_mut_ptr(),
                out.len(),
                &mut scratch,
            )
        };
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

#[cfg(all(test, any(target_arch = "x86_64", target_arch = "aarch64")))]
mod tests {
    use core::num::NonZeroU32;

    #[cfg(target_arch = "x86_64")]
    use crate::arch::pbkdf2_sha256::{
        VG_PBKDF2_HMAC_SHA256_ITERATE_SHANI_FEATURES, VG_PBKDF2_HMAC_SHA256_SHANI_FEATURES,
    };
    #[cfg(target_arch = "x86_64")]
    use crate::arch::sha256::{VG_SHA256_FINALIZE_SHANI_FEATURES, VG_SHA256_UPDATE_SHANI_FEATURES};
    #[cfg(target_arch = "x86_64")]
    use crate::cpu::Features;
    use crate::hashes::sha256::Sha256;
    use crate::pbkdf2::Pbkdf2Hash;

    /// The SHA-NI iteration and derivation need no CPU feature that the
    /// SHA-NI SHA-256 backend was not selected for.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn shani_features() {
        let backend = Features::all(&[
            VG_SHA256_UPDATE_SHANI_FEATURES,
            VG_SHA256_FINALIZE_SHANI_FEATURES,
        ]);
        assert!(backend.contains(Features::of(VG_PBKDF2_HMAC_SHA256_ITERATE_SHANI_FEATURES)));
        assert!(backend.contains(Features::of(VG_PBKDF2_HMAC_SHA256_SHANI_FEATURES)));
    }

    /// The whole verified function derives the same keys as the
    /// computation block by block that it replaces, with the SHA-256
    /// implementation selected for this CPU (on x86-64, CI runs every
    /// configuration, `VG_CPU_FEATURES`), from a password shorter and one
    /// longer than a block, for keys of zero, part of one, one and several
    /// blocks.
    #[test]
    fn whole_matches_blocks() {
        let password = [0x0b; 70];
        let salt = [0x5a; 16];
        let n = NonZeroU32::new(3).unwrap();
        for password_len in [20, 70] {
            for len in [0, 20, 32, 70] {
                let mut whole = [0u8; 70];
                let mut blocks = [0u8; 70];
                Sha256::pbkdf2_derive(&password[..password_len], &salt, n, &mut whole[..len]);
                super::super::derive_blocks::<Sha256>(
                    &password[..password_len],
                    &salt,
                    n,
                    &mut blocks[..len],
                );
                assert_eq!(whole, blocks);
            }
        }
    }
}
