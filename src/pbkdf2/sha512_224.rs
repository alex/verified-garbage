//! PBKDF2-HMAC-SHA-512/224. On x86-64, the whole derivation is
//! `vg_pbkdf2_hmac_sha512_224` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract`
//! of `VG.Spec.Hmac.sha512_224I`), the one PBKDF2 implementation for every
//! Merkle–Damgård hash function, calling SHA-512/224's verified functions: its
//! iteration calls SHA-512's verified compression function directly, twice per
//! step. It follows the implementation of SHA-512 compression that `Sha512_224`
//! runs on this CPU (`vg_pbkdf2_hmac_sha512_224_shani`,
//! `vg_pbkdf2_hmac_sha512_224_avx2`: the same verified code calling
//! `vg_sha512_compress_<suffix>`, with the same contract).
//!
//! On the other targets, the iteration is `vg_pbkdf2_hmac_sha512_224_iterate`
//! (contract `VG.Spec.Hmac.Instance.iterateContract`), the one PBKDF2 iteration
//! for every streaming hash function, calling SHA-512/224's verified streaming
//! functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(not(target_arch = "x86_64"))]
use crate::arch::pbkdf2_sha512_224::vg_pbkdf2_hmac_sha512_224_iterate;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha512_224::{
    VG_PBKDF2_HMAC_SHA512_224_AVX2_FEATURES, VG_PBKDF2_HMAC_SHA512_224_SHANI_FEATURES,
    vg_pbkdf2_hmac_sha512_224, vg_pbkdf2_hmac_sha512_224_avx2, vg_pbkdf2_hmac_sha512_224_shani,
};
use crate::hashes::sha512::{Sha512_224, Sha512_224Backend};

#[cfg(not(target_arch = "x86_64"))]
super::streaming_pbkdf2!(
    Sha512_224 (Sha512_224Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_224_iterate,
    },
    state: 192,
    scratch: 234,
    output: 28,
);

#[cfg(target_arch = "x86_64")]
super::whole_pbkdf2!(
    Sha512_224 (Sha512_224Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_224,
        ShaNi if [VG_PBKDF2_HMAC_SHA512_224_SHANI_FEATURES] => vg_pbkdf2_hmac_sha512_224_shani,
        Avx2 if [VG_PBKDF2_HMAC_SHA512_224_AVX2_FEATURES] => vg_pbkdf2_hmac_sha512_224_avx2,
    },
    scratch: 426,
    output: 28,
);
