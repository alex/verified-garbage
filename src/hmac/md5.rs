//! HMAC-MD5: `vg_hmac_md5_init`, `vg_md5_update` and `vg_hmac_md5_finalize`
//! (contracts `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.md5I`,
//! `VG.Spec.Md5.updateContract` and `VG.Spec.Hmac.Instance.finalizeContract`)
//! compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`
//! (`VG.Spec.Hmac.hmacBlockKey`), keeping the two MD5 streaming states. `init`
//! and `finalize` are the one HMAC implementation for every streaming hash
//! function, calling MD5's verified functions.
//!
//! They follow the implementation of MD5 that `Md5` runs on this CPU: on
//! x86-64 with AVX512F and AVX512VL, `vg_hmac_md5_init_avx512` and
//! `vg_hmac_md5_finalize_avx512`, the same verified code calling
//! `vg_md5_update_avx512`, `vg_md5_finalize_avx512` and
//! `vg_md5_compress_avx512`, with the same contracts.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_md5::{
    VG_HMAC_MD5_FINALIZE_AVX512_FEATURES, VG_HMAC_MD5_INIT_AVX512_FEATURES,
    vg_hmac_md5_finalize_avx512, vg_hmac_md5_init_avx512,
};
use crate::arch::hmac_md5::{vg_hmac_md5_finalize, vg_hmac_md5_init};
use crate::hashes::md5::{Md5, Md5Backend};

super::streaming_hmac!(
    Md5 (Md5Backend) {
        Scalar => (vg_hmac_md5_init, vg_hmac_md5_finalize),
        #[cfg(target_arch = "x86_64")]
        Avx512 if [VG_HMAC_MD5_INIT_AVX512_FEATURES, VG_HMAC_MD5_FINALIZE_AVX512_FEATURES] =>
            (vg_hmac_md5_init_avx512, vg_hmac_md5_finalize_avx512),
    },
    state: 80,
    scratch: 48,
    output: 16,
);
