//! HMAC-SHA-256: `vg_hmac_sha256_init`, `vg_sha256_update` and
//! `vg_hmac_sha256_finalize` compute `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`
//! (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-256 streaming states.
//!
//! On x86-64 and AArch64, `init` and `finalize` (contracts
//! `VG.Spec.Hmac.Instance.initContract` and `finalizeContract` of
//! `VG.Spec.Hmac.sha256I`) are the one HMAC implementation for every
//! streaming hash function, calling SHA-256's verified functions. On x86-64,
//! they follow the implementation of SHA-256 that `Sha256` runs on this CPU:
//! e.g. `vg_hmac_sha256_init_shani` and `vg_hmac_sha256_finalize_shani`, the
//! same verified code calling `vg_sha256_update_shani` and
//! `vg_sha256_finalize_shani`, or the `_avx2` ones. On AArch64, the `_sha2`
//! variants use the SHA-256 instructions through the same generic code.
//!
//! On ARMv7 and x86, their contracts are `VG.Spec.Hmac.initSha256Contract`
//! and `VG.Spec.Hmac.finalizeSha256Contract` (or `finalizeSha256OutContract`
//! on the 32-bit targets), with `VG.Spec.Sha256.updateContract`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
use super::{HmacHash, sealed};
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

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
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
    scratch: 104,
    output: 32,
);

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
impl super::Hmac<Sha256> {
    /// The key's two SHA-256 streaming states, for `K₀ ⊕ ipad` and then
    /// `K₀ ⊕ opad`, as `vg_hmac_sha256_init` left them (the arguments of
    /// `vg_pbkdf2_hmac_sha256_iterate`), for a computation that has not
    /// absorbed any data yet.
    pub(crate) fn sha256_key_states(&self) -> [u8; 192] {
        debug_assert_eq!(self.state.count, Sha256::BLOCK_SIZE as u64);
        let mut key = [0u8; 192];
        key[..96].copy_from_slice(&self.state.inner);
        key[96..].copy_from_slice(&self.state.outer);
        key
    }
}

/// An HMAC-SHA-256 computation: the SHA-256 streaming states for the inner
/// hash, which represents `(K₀ ⊕ ipad) ‖ text`, and the outer one, which
/// represents `K₀ ⊕ opad`, and the length of the inner message.
#[cfg(any(target_arch = "arm", target_arch = "x86"))]
#[doc(hidden)]
#[derive(Clone)]
pub struct Sha256HmacState {
    inner: [u8; 96],
    outer: [u8; 96],
    /// The length of `(K₀ ⊕ ipad) ‖ text`, in bytes (modulo 2⁶⁴).
    count: u64,
    /// The implementation of `vg_sha256_update` this CPU runs.
    backend: Sha256Backend,
}

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
impl Drop for Sha256HmacState {
    /// Wipes the streaming states, which represent the key.
    fn drop(&mut self) {
        crate::zeroize::zeroize(&mut self.inner);
        crate::zeroize::zeroize(&mut self.outer);
    }
}

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
impl sealed::Sealed for Sha256 {}

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
impl HmacHash for Sha256 {
    type State = Sha256HmacState;

    fn hmac_init(key: &[u8]) -> Sha256HmacState {
        assert!(key.len() <= Self::BLOCK_SIZE);
        let mut state = Sha256HmacState {
            inner: [0; 96],
            outer: [0; 96],
            count: Self::BLOCK_SIZE as u64,
            backend: Sha256Backend::select(crate::cpu::detected()),
        };
        let mut scratch = [0u64; 76];
        // SAFETY: `key.len()` is at most 64; `state.inner` and `state.outer`
        // are valid for reads and writes of 96 bytes, `key` for reads of
        // `key.len()` bytes and `scratch` for reads and writes of 608 bytes;
        // they are distinct objects, so they do not overlap each other or the
        // call's stack frame, nor wrap around the address space.
        unsafe {
            vg_hmac_sha256_init(
                &mut state.inner,
                &mut state.outer,
                key.as_ptr(),
                key.len(),
                &mut scratch,
            )
        };
        state
    }

    fn hmac_update(state: &mut Sha256HmacState, data: &[u8]) {
        let mut scratch = [0u64; 76];
        // SAFETY: `state.inner` is valid for reads and writes of 96 bytes,
        // `data` for reads of `data.len()` bytes and `scratch` for reads and
        // writes of 608 bytes; they are distinct objects, so they do not
        // overlap each other or the call's stack frame, nor wrap around the
        // address space. `state.count` is the length of the message
        // `state.inner` represents, modulo 2⁶⁴. `state.backend` was
        // selected for this CPU's features.
        unsafe {
            state.backend.update(
                &mut state.inner,
                state.count,
                data.as_ptr(),
                data.len(),
                &mut scratch,
            )
        };
        state.count = state.count.wrapping_add(data.len() as u64);
    }

    fn hmac_finalize(mut state: Sha256HmacState) -> [u8; 32] {
        let mut mac = [0u8; 32];
        let mut scratch = [0u64; 86];
        // SAFETY: `state.inner` is valid for reads and writes of 96 bytes,
        // `state.outer` for reads of 96 bytes, `mac` for writes of 32 bytes
        // and `scratch` for reads and writes of 688 bytes; they are distinct
        // objects, so they do not overlap each other or the call's stack
        // frame, nor wrap around the address space. `state.inner` represents
        // `(K₀ ⊕ ipad) ‖ text`, of `state.count` bytes, and `state.outer`
        // represents `K₀ ⊕ opad`.
        unsafe {
            vg_hmac_sha256_finalize(
                &mut state.inner,
                &state.outer,
                state.count,
                &mut mac,
                &mut scratch,
            )
        };
        mac
    }
}
