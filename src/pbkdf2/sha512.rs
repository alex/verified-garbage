//! PBKDF2-HMAC-SHA-512. On x86-64, the whole derivation is
//! `vg_pbkdf2_hmac_sha512` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha512I`), the one PBKDF2 implementation for every
//! Merkle–Damgård hash function, calling SHA-512's verified functions: its
//! iteration calls SHA-512's verified compression function directly, twice per
//! step. It follows the implementation of SHA-512 compression that `Sha512`
//! runs on this CPU (`vg_pbkdf2_hmac_sha512_shani`,
//! `vg_pbkdf2_hmac_sha512_avx2`: the same verified code calling
//! `vg_sha512_compress_<suffix>`, with the same contract).
//!
//! On the other targets, the iteration is `vg_pbkdf2_hmac_sha512_iterate`
//! (contract `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration
//! for every streaming hash function, calling SHA-512's verified streaming
//! functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(not(target_arch = "x86_64"))]
use crate::arch::pbkdf2_sha512::vg_pbkdf2_hmac_sha512_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha512::{
    VG_PBKDF2_HMAC_SHA512_AVX2_FEATURES, VG_PBKDF2_HMAC_SHA512_SHANI_FEATURES,
    vg_pbkdf2_hmac_sha512, vg_pbkdf2_hmac_sha512_avx2, vg_pbkdf2_hmac_sha512_shani,
};
use crate::hashes::sha512::{Sha512, Sha512Backend};

#[cfg(not(target_arch = "x86_64"))]
super::streaming_pbkdf2!(
    Sha512 (Sha512Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_iterate,
    },
    state: 192,
    scratch: 234,
    output: 64,
);

#[cfg(target_arch = "x86_64")]
super::whole_pbkdf2!(
    Sha512 (Sha512Backend) {
        Scalar => vg_pbkdf2_hmac_sha512,
        ShaNi if [VG_PBKDF2_HMAC_SHA512_SHANI_FEATURES] => vg_pbkdf2_hmac_sha512_shani,
        Avx2 if [VG_PBKDF2_HMAC_SHA512_AVX2_FEATURES] => vg_pbkdf2_hmac_sha512_avx2,
    },
    scratch: 426,
    output: 64,
);
