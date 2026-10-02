//! PBKDF2-HMAC-SHA-256 (RFC 8018 §5.2).
//!
//! The whole derivation is `vg_pbkdf2_hmac_sha256` (contract
//! `VG.Spec.Hmac.Instance.pbkdf2Contract` of `VG.Spec.Hmac.sha256I`). On x86-64
//! and AArch64, it is the one PBKDF2 implementation for every Merkle–Damgård
//! hash function, calling SHA-256's verified functions. On x86-64, it follows the
//! implementation of SHA-256 that `Sha256` runs on this CPU:
//! `vg_pbkdf2_hmac_sha256_shani` with the SHA extensions, the same verified
//! code calling `vg_sha256_compress_shani`, with the same contract; likewise
//! `vg_pbkdf2_hmac_sha256_avx2` with AVX2. AArch64 selects
//! `vg_pbkdf2_hmac_sha256_sha2` when the SHA-256 instructions are available.
//!
//! On ARMv7 and x86, the whole derivation is the one for every streaming hash
//! function, calling SHA-256's verified streaming functions, HMAC-SHA-256's
//! `init` and `finalize` and `vg_pbkdf2_hmac_sha256_iterate` (contract
//! `VG.Spec.Pbkdf2.iterateSha256Contract`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use core::num::NonZeroU32;

use crate::arch::pbkdf2_sha256::vg_pbkdf2_hmac_sha256;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha256::{
    VG_PBKDF2_HMAC_SHA256_AVX2_FEATURES, VG_PBKDF2_HMAC_SHA256_SHANI_FEATURES,
    vg_pbkdf2_hmac_sha256_avx2, vg_pbkdf2_hmac_sha256_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::pbkdf2_sha256::{VG_PBKDF2_HMAC_SHA256_SHA2_FEATURES, vg_pbkdf2_hmac_sha256_sha2};
use crate::hashes::sha256::{Sha256, Sha256Backend};

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
