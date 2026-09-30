//! PBKDF2-HMAC-SHA-512: the iteration is `vg_pbkdf2_hmac_sha512_iterate`
//! (contract `VG.Spec.Hmac.Instance.iterateContract` of
//! `VG.Spec.Hmac.sha512I`). On x86-64 it is the one iteration for every hash
//! function whose streaming code is the generic one, calling SHA-512's verified
//! compression function directly, twice per step; on the other targets, the one
//! iteration for every streaming hash function, calling SHA-512's verified
//! streaming functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::pbkdf2_sha512::vg_pbkdf2_hmac_sha512_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha512::{
    VG_PBKDF2_HMAC_SHA512_ITERATE_AVX2_FEATURES, VG_PBKDF2_HMAC_SHA512_ITERATE_SHANI_FEATURES,
    vg_pbkdf2_hmac_sha512_iterate_avx2, vg_pbkdf2_hmac_sha512_iterate_shani,
};
use crate::hashes::sha512::{Sha512, Sha512Backend};

super::streaming_pbkdf2!(
    Sha512 (Sha512Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_iterate,
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_PBKDF2_HMAC_SHA512_ITERATE_SHANI_FEATURES] => vg_pbkdf2_hmac_sha512_iterate_shani,
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_PBKDF2_HMAC_SHA512_ITERATE_AVX2_FEATURES] => vg_pbkdf2_hmac_sha512_iterate_avx2,
    },
    state: 192,
    scratch: 234,
    output: 64,
);
