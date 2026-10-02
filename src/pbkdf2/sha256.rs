//! PBKDF2-HMAC-SHA-256 (RFC 8018 §5.2).
//!
//! On x86-64 and AArch64, the whole derivation is `vg_pbkdf2_hmac_sha256`
//! (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of `VG.Spec.Hmac.sha256I`),
//! the one PBKDF2 implementation for every Merkle–Damgård hash function,
//! calling SHA-256's verified functions. On x86-64, it follows the
//! implementation of SHA-256 that `Sha256` runs on this CPU:
//! `vg_pbkdf2_hmac_sha256_shani` with the SHA extensions, the same verified
//! code calling `vg_sha256_compress_shani`, with the same contract; likewise
//! `vg_pbkdf2_hmac_sha256_avx2` with AVX2. AArch64 selects
//! `vg_pbkdf2_hmac_sha256_sha2` when the SHA-256 instructions are available.
//!
//! On ARMv7 and x86, for each block `Tᵢ` of the derived key,
//! `U₁ = HMAC (P, S ‖ INT (i))` is the verified HMAC-SHA-256 (`Hmac`), and
//! the rest of the chain, `Uⱼ₊₁ = HMAC (P, Uⱼ)` exclusive-or'ed into
//! `Tᵢ = U₁ ⊕ … ⊕ U_c`, is the verified `vg_pbkdf2_hmac_sha256_iterate`
//! (contract `VG.Spec.Pbkdf2.iterateSha256Contract`), from the streaming
//! states that the HMAC computation starts from (see `super`, which splits
//! the derived key into blocks).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
use core::num::NonZeroU32;

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use crate::arch::pbkdf2_sha256::vg_pbkdf2_hmac_sha256;
#[cfg(any(target_arch = "arm", target_arch = "x86"))]
use crate::arch::pbkdf2_sha256::vg_pbkdf2_hmac_sha256_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha256::{
    VG_PBKDF2_HMAC_SHA256_AVX2_FEATURES, VG_PBKDF2_HMAC_SHA256_SHANI_FEATURES,
    vg_pbkdf2_hmac_sha256_avx2, vg_pbkdf2_hmac_sha256_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::pbkdf2_sha256::{VG_PBKDF2_HMAC_SHA256_SHA2_FEATURES, vg_pbkdf2_hmac_sha256_sha2};
use crate::hashes::sha256::Sha256;
#[cfg(not(target_arch = "arm"))]
use crate::hashes::sha256::Sha256Backend;

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
super::whole_pbkdf2!(
    Sha256 (Sha256Backend) {
        Scalar => vg_pbkdf2_hmac_sha256,
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_PBKDF2_HMAC_SHA256_SHA2_FEATURES] =>
            vg_pbkdf2_hmac_sha256_sha2,
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_PBKDF2_HMAC_SHA256_SHANI_FEATURES] => vg_pbkdf2_hmac_sha256_shani,
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_PBKDF2_HMAC_SHA256_AVX2_FEATURES] => vg_pbkdf2_hmac_sha256_avx2,
    },
    scratch: 200,
    output: 32,
);

/// Repeats `U ← HMAC (K₀, U)`, `T ← T ⊕ U` `n` times, from `U = *u` and
/// `T = *t`, leaving the final `T` in `*t`, for the streaming states `key`
/// of `K₀ ⊕ ipad` and `K₀ ⊕ opad`.
#[cfg(any(target_arch = "arm", target_arch = "x86"))]
fn iterate(key: &[u8; 192], u: &[u8; 32], n: u32, t: &mut [u8; 32]) {
    let mut scratch = [0u64; 104];
    // SAFETY: `key` is valid for reads of 192 bytes, `u` for reads of 32
    // bytes, `t` for reads and writes of 32 bytes and `scratch` for reads and
    // writes of 832 bytes; `t` and `scratch` are distinct objects from each
    // other and the others (`key` and `u` are only read), so they do not
    // overlap each other, the stack arguments, the return address and the
    // stack below it (on x86), nor wrap around the address
    // space. `key` holds the streaming states for `K₀ ⊕ ipad` and `K₀ ⊕ opad`
    // that `vg_hmac_sha256_init` left.
    #[cfg(target_arch = "arm")]
    unsafe {
        vg_pbkdf2_hmac_sha256_iterate(key, u, n, t, &mut scratch)
    };
    #[cfg(target_arch = "x86")]
    {
        let iterate = match Sha256Backend::select(crate::cpu::detected()) {
            Sha256Backend::Scalar => vg_pbkdf2_hmac_sha256_iterate,
        };
        // SAFETY: the buffers satisfy the contract described above; selecting
        // the hash backend also selects every PBKDF2 caller of that backend.
        unsafe { iterate(key, u, n, t, &mut scratch) };
    }
}

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
impl super::Pbkdf2Hash for Sha256 {
    fn pbkdf2_derive(password: &[u8], salt: &[u8], iterations: NonZeroU32, out: &mut [u8]) {
        super::derive_blocks::<Sha256, [u8; 192]>(
            password,
            salt,
            iterations,
            out,
            |prf| prf.sha256_key_states(),
            iterate,
        );
    }
}
