//! HMAC-SHA-512: `vg_hmac_sha512_init`, `vg_sha512_update` and
//! `vg_hmac_sha512_finalize` (contracts `VG.Spec.Hmac.Instance.initContract` of
//! `VG.Spec.Hmac.sha512I`, `VG.Spec.Sha512.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕
//! ipad) ‖ text))` (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-512
//! streaming states. `init` and `finalize` are the one HMAC implementation for
//! every streaming hash function, calling SHA-512's verified functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha512::{
    VG_HMAC_SHA512_FINALIZE_AVX2_FEATURES, VG_HMAC_SHA512_INIT_AVX2_FEATURES,
    vg_hmac_sha512_finalize_avx2, vg_hmac_sha512_init_avx2,
};
use crate::arch::hmac_sha512::{vg_hmac_sha512_finalize, vg_hmac_sha512_init};
use crate::hashes::sha512::{Sha512, Sha512Backend};

super::streaming_hmac!(
    Sha512 (Sha512Backend) {
        Scalar => (vg_hmac_sha512_init, vg_hmac_sha512_finalize),
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_HMAC_SHA512_INIT_AVX2_FEATURES, VG_HMAC_SHA512_FINALIZE_AVX2_FEATURES] =>
            (vg_hmac_sha512_init_avx2, vg_hmac_sha512_finalize_avx2),
    },
    state: 192,
    scratch: 234,
    output: 64,
);
