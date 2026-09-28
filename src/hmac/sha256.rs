//! HMAC-SHA-256: `vg_hmac_sha256_init`, `vg_sha256_update` and
//! `vg_hmac_sha256_finalize` (contracts `VG.Spec.Hmac.Instance.initContract`
//! of `VG.Spec.Hmac.sha256I`, `VG.Spec.Sha256.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕
//! ipad) ‖ text))` (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-256
//! streaming states. `init` and `finalize` are the one HMAC implementation
//! for every Merkle–Damgård hash function, calling SHA-256's verified
//! functions.
//!
//! They follow the implementation of SHA-256 that `Sha256` runs on this CPU:
//! on x86-64 and x86, e.g. `vg_hmac_sha256_init_shani` and
//! `vg_hmac_sha256_finalize_shani`, the same verified code calling SHA-256's
//! `_shani` functions, with the same contracts, or on x86-64 the `_avx2`
//! ones. On AArch64, the `_sha2` variants use the SHA-256 instructions
//! through the same generic code.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha256::{
    VG_HMAC_SHA256_FINALIZE_AVX2_FEATURES, VG_HMAC_SHA256_INIT_AVX2_FEATURES,
    vg_hmac_sha256_finalize_avx2, vg_hmac_sha256_init_avx2,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::hmac_sha256::{
    VG_HMAC_SHA256_FINALIZE_SHA2_FEATURES, VG_HMAC_SHA256_INIT_SHA2_FEATURES,
    vg_hmac_sha256_finalize_sha2, vg_hmac_sha256_init_sha2,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::hmac_sha256::{
    VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES, VG_HMAC_SHA256_INIT_SHANI_FEATURES,
    vg_hmac_sha256_finalize_shani, vg_hmac_sha256_init_shani,
};
use crate::arch::hmac_sha256::{vg_hmac_sha256_finalize, vg_hmac_sha256_init};
use crate::hashes::sha256::{Sha256, Sha256Backend};

super::streaming_hmac!(
    Sha256 (Sha256Backend) {
        Scalar => (vg_hmac_sha256_init, vg_hmac_sha256_finalize),
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_HMAC_SHA256_INIT_SHA2_FEATURES, VG_HMAC_SHA256_FINALIZE_SHA2_FEATURES] =>
            (vg_hmac_sha256_init_sha2, vg_hmac_sha256_finalize_sha2),
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        ShaNi if [VG_HMAC_SHA256_INIT_SHANI_FEATURES, VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES] =>
            (vg_hmac_sha256_init_shani, vg_hmac_sha256_finalize_shani),
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_HMAC_SHA256_INIT_AVX2_FEATURES, VG_HMAC_SHA256_FINALIZE_AVX2_FEATURES] =>
            (vg_hmac_sha256_init_avx2, vg_hmac_sha256_finalize_avx2),
    },
    state: 96,
    scratch: 104,
    output: 32,
);
