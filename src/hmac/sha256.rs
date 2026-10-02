//! HMAC-SHA-256: `vg_hmac_sha256_init`, `vg_sha256_update` and
//! `vg_hmac_sha256_finalize` (contracts
//! `VG.Spec.Hmac.Instance.initAnyKeyContract` of `VG.Spec.Hmac.sha256I`,
//! `VG.Spec.Sha256.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute `H((K₀ ⊕ opad) ‖ H((K₀
//! ⊕ ipad) ‖ text))` (`VG.Spec.Hmac.hmac`), keeping the two SHA-256
//! streaming states. `init` and `finalize` are the one HMAC implementation
//! for every streaming hash function, calling SHA-256's verified functions.
//!
//! They follow the implementation of SHA-256 that `Sha256` runs on this CPU:
//! on x86-64, e.g. `vg_hmac_sha256_init_shani` and
//! `vg_hmac_sha256_finalize_shani`, the same verified code calling
//! `vg_sha256_update_shani` and `vg_sha256_finalize_shani`, or the `_avx2`
//! ones. On AArch64, the `_sha2` variants use the SHA-256 instructions through
//! the same generic code.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha256::{
    VG_HMAC_SHA256_FINALIZE_AVX2_FEATURES, VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES,
    VG_HMAC_SHA256_INIT_AVX2_FEATURES, VG_HMAC_SHA256_INIT_SHANI_FEATURES,
    vg_hmac_sha256_finalize_avx2, vg_hmac_sha256_finalize_shani, vg_hmac_sha256_init_avx2,
    vg_hmac_sha256_init_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::hmac_sha256::{
    VG_HMAC_SHA256_FINALIZE_SHA2_FEATURES, VG_HMAC_SHA256_INIT_SHA2_FEATURES,
    vg_hmac_sha256_finalize_sha2, vg_hmac_sha256_init_sha2,
};
use crate::arch::hmac_sha256::{vg_hmac_sha256_finalize, vg_hmac_sha256_init};
use crate::hashes::sha256::{Sha256, Sha256Backend};

super::streaming_hmac!(
    Sha256 (Sha256Backend) {
        Scalar => (vg_hmac_sha256_init, vg_hmac_sha256_finalize),
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_HMAC_SHA256_INIT_SHA2_FEATURES, VG_HMAC_SHA256_FINALIZE_SHA2_FEATURES] =>
            (vg_hmac_sha256_init_sha2, vg_hmac_sha256_finalize_sha2),
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_HMAC_SHA256_INIT_SHANI_FEATURES, VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES] =>
            (vg_hmac_sha256_init_shani, vg_hmac_sha256_finalize_shani),
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_HMAC_SHA256_INIT_AVX2_FEATURES, VG_HMAC_SHA256_FINALIZE_AVX2_FEATURES] =>
            (vg_hmac_sha256_init_avx2, vg_hmac_sha256_finalize_avx2),
    },
    state: 96,
    init_scratch: 200,
    finalize_scratch: 104,
    output: 32,
);

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
impl super::Hmac<Sha256> {
    /// The key's two SHA-256 streaming states, for `K₀ ⊕ ipad` and then
    /// `K₀ ⊕ opad`, as `vg_hmac_sha256_init` left them (the arguments of
    /// `vg_pbkdf2_hmac_sha256_iterate`), for a computation that has not
    /// absorbed any data yet.
    pub(crate) fn sha256_key_states(&self) -> [u8; 192] {
        let (mut inner, count) = self.state().inner.state();
        debug_assert_eq!(count, Sha256::BLOCK_SIZE as u64);
        let mut key = [0u8; 192];
        key[..96].copy_from_slice(&inner);
        key[96..].copy_from_slice(&self.state().outer);
        crate::zeroize::zeroize(&mut inner);
        key
    }
}
