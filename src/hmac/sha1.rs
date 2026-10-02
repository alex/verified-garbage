//! HMAC-SHA-1: `vg_hmac_sha1_init`, `vg_sha1_update` and
//! `vg_hmac_sha1_finalize` (contracts `VG.Spec.Hmac.Instance.initAnyKeyContract` of
//! `VG.Spec.Hmac.sha1I`, `VG.Spec.Sha1.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕
//! ipad) ‖ text))` (`VG.Spec.Hmac.hmac`), keeping the two SHA-1
//! streaming states. `init` and `finalize` are the one HMAC implementation for
//! every streaming hash function, calling SHA-1's verified functions.
//!
//! They follow the implementation of SHA-1 that `Sha1` runs on this CPU: on
//! x86-64 with the SHA extensions, `vg_hmac_sha1_init_shani` and
//! `vg_hmac_sha1_finalize_shani`, the same verified code calling
//! `vg_sha1_update_shani` and `vg_sha1_finalize_shani`, with the same
//! contracts.

//! On AArch64, the `_sha2` variants follow SHA-1 hardware dispatch.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::hmac_sha1::{
    VG_HMAC_SHA1_FINALIZE_SHA2_FEATURES, VG_HMAC_SHA1_INIT_SHA2_FEATURES,
    vg_hmac_sha1_finalize_sha2, vg_hmac_sha1_init_sha2,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha1::{
    VG_HMAC_SHA1_FINALIZE_SHANI_FEATURES, VG_HMAC_SHA1_INIT_SHANI_FEATURES,
    vg_hmac_sha1_finalize_shani, vg_hmac_sha1_init_shani,
};
use crate::arch::hmac_sha1::{vg_hmac_sha1_finalize, vg_hmac_sha1_init};
use crate::hashes::sha1::{Sha1, Sha1Backend};

super::streaming_hmac!(
    Sha1 (Sha1Backend) {
        Scalar => (vg_hmac_sha1_init, vg_hmac_sha1_finalize),
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_HMAC_SHA1_INIT_SHA2_FEATURES, VG_HMAC_SHA1_FINALIZE_SHA2_FEATURES] =>
            (vg_hmac_sha1_init_sha2, vg_hmac_sha1_finalize_sha2),
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_HMAC_SHA1_INIT_SHANI_FEATURES, VG_HMAC_SHA1_FINALIZE_SHANI_FEATURES] =>
            (vg_hmac_sha1_init_shani, vg_hmac_sha1_finalize_shani),
    },
    state: 84,
    init_scratch: 140,
    finalize_scratch: 56,
    output: 20,
);
