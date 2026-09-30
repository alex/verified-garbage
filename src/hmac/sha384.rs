//! HMAC-SHA-384: `vg_hmac_sha384_init`, `vg_sha512_update` and
//! `vg_hmac_sha384_finalize` (contracts `VG.Spec.Hmac.Instance.initContract` of
//! `VG.Spec.Hmac.sha384I`, `VG.Spec.Sha512.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕
//! ipad) ‖ text))` (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-384
//! streaming states. `init` and `finalize` are the one HMAC implementation for
//! every streaming hash function, calling SHA-384's verified functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha384::{
    VG_HMAC_SHA384_FINALIZE_AVX2_FEATURES, VG_HMAC_SHA384_INIT_AVX2_FEATURES,
    vg_hmac_sha384_finalize_avx2, vg_hmac_sha384_init_avx2,
};
use crate::arch::hmac_sha384::{vg_hmac_sha384_finalize, vg_hmac_sha384_init};
use crate::hashes::sha512::{Sha384, Sha384Backend};

super::streaming_hmac!(
    Sha384 (Sha384Backend) {
        Scalar => (vg_hmac_sha384_init, vg_hmac_sha384_finalize),
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_HMAC_SHA384_INIT_AVX2_FEATURES, VG_HMAC_SHA384_FINALIZE_AVX2_FEATURES] =>
            (vg_hmac_sha384_init_avx2, vg_hmac_sha384_finalize_avx2),
    },
    state: 192,
    scratch: 234,
    output: 48,
);
