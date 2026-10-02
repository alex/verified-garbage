//! HMAC-SHA-512/256: `vg_hmac_sha512_256_init`, `vg_sha512_update` and
//! `vg_hmac_sha512_256_finalize` (contracts
//! `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha512_256I`,
//! `VG.Spec.Sha512.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕
//! ipad) ‖ text))` (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-512/256
//! streaming states. `init` and `finalize` are the one HMAC implementation for
//! every streaming hash function, calling SHA-512/256's verified functions.
//!
//! On AArch64, the `_sha3` variants follow SHA-512 hardware dispatch.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha512_256::{
    VG_HMAC_SHA512_256_FINALIZE_AVX2_FEATURES, VG_HMAC_SHA512_256_FINALIZE_SHANI_FEATURES,
    VG_HMAC_SHA512_256_INIT_AVX2_FEATURES, VG_HMAC_SHA512_256_INIT_SHANI_FEATURES,
    vg_hmac_sha512_256_finalize_avx2, vg_hmac_sha512_256_finalize_shani,
    vg_hmac_sha512_256_init_avx2, vg_hmac_sha512_256_init_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::hmac_sha512_256::{
    VG_HMAC_SHA512_256_FINALIZE_SHA3_FEATURES, VG_HMAC_SHA512_256_INIT_SHA3_FEATURES,
    vg_hmac_sha512_256_finalize_sha3, vg_hmac_sha512_256_init_sha3,
};
use crate::arch::hmac_sha512_256::{vg_hmac_sha512_256_finalize, vg_hmac_sha512_256_init};
use crate::hashes::sha512_256::{Sha512_256, Sha512_256Backend};

super::streaming_hmac!(
    Sha512_256 (Sha512_256Backend) {
        Scalar => (vg_hmac_sha512_256_init, vg_hmac_sha512_256_finalize),
        #[cfg(target_arch = "aarch64")]
        Sha3 if [VG_HMAC_SHA512_256_INIT_SHA3_FEATURES, VG_HMAC_SHA512_256_FINALIZE_SHA3_FEATURES] =>
            (vg_hmac_sha512_256_init_sha3, vg_hmac_sha512_256_finalize_sha3),
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_HMAC_SHA512_256_INIT_SHANI_FEATURES, VG_HMAC_SHA512_256_FINALIZE_SHANI_FEATURES] =>
            (vg_hmac_sha512_256_init_shani, vg_hmac_sha512_256_finalize_shani),
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_HMAC_SHA512_256_INIT_AVX2_FEATURES, VG_HMAC_SHA512_256_FINALIZE_AVX2_FEATURES] =>
            (vg_hmac_sha512_256_init_avx2, vg_hmac_sha512_256_finalize_avx2),
    },
    state: 192,
    scratch: 234,
    output: 32,
);
