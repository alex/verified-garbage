//! HMAC-SHA-256: `vg_hmac_sha256_init`, `vg_sha256_update` and
//! `vg_hmac_sha256_finalize` (contracts `VG.Spec.Hmac.initSha256Contract`,
//! `VG.Spec.Sha256.updateContract` and `VG.Spec.Hmac.finalizeSha256Contract`,
//! or `finalizeSha256OutContract` on the 32-bit targets) compute
//! `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`
//! (`VG.Spec.Hmac.hmacBlockKey`), keeping the two SHA-256 streaming states.
//! (`vg_sha256_update` is whichever implementation `Sha256` would use on
//! this CPU, e.g. `vg_sha256_update_shani`, with the same contract; on
//! x86-64, `init` and `finalize` follow it, e.g. `vg_hmac_sha256_init_shani`
//! and `vg_hmac_sha256_finalize_shani`, the same verified code calling
//! `vg_sha256_compress_shani`.)

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use super::{HmacHash, sealed};
use crate::arch::hmac_sha256::{vg_hmac_sha256_finalize, vg_hmac_sha256_init};
#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha256::{vg_hmac_sha256_finalize_shani, vg_hmac_sha256_init_shani};
use crate::hashes::sha256::{Sha256, Sha256Backend};

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

    /// The implementation of SHA-256 this computation runs, chosen for this
    /// CPU.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn sha256_backend(&self) -> Sha256Backend {
        self.state.backend
    }
}

/// An HMAC-SHA-256 computation: the SHA-256 streaming states for the inner
/// hash, which represents `(K₀ ⊕ ipad) ‖ text`, and the outer one, which
/// represents `K₀ ⊕ opad`, and the length of the inner message.
#[doc(hidden)]
#[derive(Clone)]
pub struct Sha256HmacState {
    inner: [u8; 96],
    outer: [u8; 96],
    /// The length of `(K₀ ⊕ ipad) ‖ text`, in bytes (modulo 2⁶⁴).
    count: u64,
    /// The implementation of `vg_sha256_update` (and, on x86-64, of `init`
    /// and `finalize`) this CPU runs.
    backend: Sha256Backend,
}

impl sealed::Sealed for Sha256 {}

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
        #[cfg(target_arch = "x86_64")]
        let init = match state.backend {
            Sha256Backend::Scalar => vg_hmac_sha256_init,
            Sha256Backend::ShaNi => vg_hmac_sha256_init_shani,
        };
        #[cfg(not(target_arch = "x86_64"))]
        let init = vg_hmac_sha256_init;
        let mut scratch = [0u64; 76];
        // SAFETY: `key.len()` is at most 64; `state.inner` and `state.outer`
        // are valid for reads and writes of 96 bytes, `key` for reads of
        // `key.len()` bytes and `scratch` for reads and writes of 608 bytes;
        // they are distinct objects, so they do not overlap each other or the
        // call's stack frame, nor wrap around the address space. On x86-64,
        // `init` needs the CPU features of `state.backend`, which were
        // detected (`tests::shani_features`).
        unsafe {
            init(
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

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    fn hmac_finalize(mut state: Sha256HmacState) -> [u8; 32] {
        #[cfg(target_arch = "x86_64")]
        let finalize = match state.backend {
            Sha256Backend::Scalar => vg_hmac_sha256_finalize,
            Sha256Backend::ShaNi => vg_hmac_sha256_finalize_shani,
        };
        #[cfg(not(target_arch = "x86_64"))]
        let finalize = vg_hmac_sha256_finalize;
        let mut scratch = [0u64; 86];
        // SAFETY: `state.inner` is valid for reads and writes of 96 bytes,
        // `state.outer` for reads of 96 bytes and `scratch` for reads and
        // writes of 688 bytes; they are distinct objects, so they do not
        // overlap each other or (on x86-64) the return address. `state.inner`
        // represents `(K₀ ⊕ ipad) ‖ text`, of `state.count` bytes, and
        // `state.outer` represents `K₀ ⊕ opad`. On x86-64, `finalize` needs
        // the CPU features of `state.backend`, which were detected
        // (`tests::shani_features`).
        unsafe { finalize(&mut state.inner, &state.outer, state.count, &mut scratch) };
        // The MAC is in bytes 176 to 207 of `scratch`.
        let mut mac = [0u8; 32];
        for (out, word) in mac.as_chunks_mut::<8>().0.iter_mut().zip(&scratch[22..26]) {
            *out = word.to_ne_bytes();
        }
        mac
    }

    #[cfg(any(target_arch = "arm", target_arch = "x86"))]
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

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use crate::arch::hmac_sha256::{
        VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES, VG_HMAC_SHA256_INIT_SHANI_FEATURES,
    };
    use crate::arch::sha256::{VG_SHA256_FINALIZE_SHANI_FEATURES, VG_SHA256_UPDATE_SHANI_FEATURES};
    use crate::cpu::Features;

    /// The SHA-NI `init` and `finalize` need no CPU feature that the SHA-NI
    /// SHA-256 backend was not selected for.
    #[test]
    fn shani_features() {
        let backend = Features::all(&[
            VG_SHA256_UPDATE_SHANI_FEATURES,
            VG_SHA256_FINALIZE_SHANI_FEATURES,
        ]);
        assert!(backend.contains(Features::of(VG_HMAC_SHA256_INIT_SHANI_FEATURES)));
        assert!(backend.contains(Features::of(VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES)));
    }
}
