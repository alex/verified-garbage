//! PBKDF2-HMAC-SHA-512/256. On x86-64 and AArch64, the whole derivation is
//! `vg_pbkdf2_hmac_sha512_256` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha512_256I`), the one PBKDF2 implementation for every
//! Merkle–Damgård hash function, calling SHA-512/256's verified functions: its
//! iteration calls SHA-512's verified compression function directly, twice per
//! step. On x86-64, it follows the implementation of SHA-512 compression that
//! `Sha512_256` runs on this CPU (`vg_pbkdf2_hmac_sha512_256_shani`,
//! `vg_pbkdf2_hmac_sha512_256_avx2`: the same verified code calling
//! `vg_sha512_compress_<suffix>`, with the same contract).
//!
//! On ARMv7 and x86, the iteration is `vg_pbkdf2_hmac_sha512_256_iterate` (contract
//! `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration for every
//! streaming hash function, calling SHA-512/256's verified streaming functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use crate::arch::pbkdf2_sha512_256::vg_pbkdf2_hmac_sha512_256;
#[cfg(any(target_arch = "arm", target_arch = "x86"))]
use crate::arch::pbkdf2_sha512_256::vg_pbkdf2_hmac_sha512_256_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha512_256::{
    VG_PBKDF2_HMAC_SHA512_256_AVX2_FEATURES, VG_PBKDF2_HMAC_SHA512_256_SHANI_FEATURES,
    vg_pbkdf2_hmac_sha512_256_avx2, vg_pbkdf2_hmac_sha512_256_shani,
};
use crate::hashes::sha512::{Sha512_256, Sha512_256Backend};

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
super::streaming_pbkdf2!(
    Sha512_256 (Sha512_256Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_256_iterate,
    },
    state: 192,
    scratch: 234,
    output: 32,
);

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
super::whole_pbkdf2!(
    Sha512_256 (Sha512_256Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_256,
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_PBKDF2_HMAC_SHA512_256_SHANI_FEATURES] => vg_pbkdf2_hmac_sha512_256_shani,
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_PBKDF2_HMAC_SHA512_256_AVX2_FEATURES] => vg_pbkdf2_hmac_sha512_256_avx2,
    },
    scratch: 426,
    output: 32,
);
