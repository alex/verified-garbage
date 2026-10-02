//! The implementations of AES, which everything built on it follows:
//! AES-GCM (`crate::aes_gcm`) and AES-CMAC (`crate::cmac::aes`) each choose
//! one [`Backend`], and run its key expansion and its counter mode, directly
//! or through their own functions for it (e.g. `vg_cmac_aes_update_aesni`
//! calls `vg_aes_ctr32_aesni`). Those functions may need more features than
//! AES's own (GCM's `vg_ghash_pclmul` needs PCLMULQDQ), so on targets with
//! more than one implementation each caller selects with
//! `Backend::select_for`, passing theirs: a CPU without them runs the scalar
//! implementation.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::aes::{VG_AES_CTR32_AES_FEATURES, VG_AES_EXPAND_KEY_AES_FEATURES};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes::{VG_AES_CTR32_AESNI_FEATURES, VG_AES_EXPAND_KEY_AESNI_FEATURES};
use crate::cpu::Features;

/// The implementations of `vg_aes_expand_key` and `vg_aes_ctr32`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// Constant-time scalar code, for the target's baseline ISA.
    Scalar,
    /// AES-NI: the `_aesni` functions.
    #[cfg(target_arch = "x86_64")]
    AesNi,
    /// The AES extension: the `_aes` functions.
    #[cfg(target_arch = "aarch64")]
    Aes,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run, for a
    /// caller whose own functions for AES-NI need the features in `aesni`
    /// (besides those of `vg_aes_expand_key_aesni` and `vg_aes_ctr32_aesni`,
    /// which this checks).
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select_for(f: Features, aesni: &[&[&str]]) -> Backend {
        let own = Features::all(&[
            VG_AES_EXPAND_KEY_AESNI_FEATURES,
            VG_AES_CTR32_AESNI_FEATURES,
        ]);
        if f.contains(own) && f.contains(Features::all(aesni)) {
            Backend::AesNi
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run, for a
    /// caller whose own functions for the AES extension need the features
    /// in `aes` (besides those of `vg_aes_expand_key_aes` and
    /// `vg_aes_ctr32_aes`, which this checks).
    #[cfg(target_arch = "aarch64")]
    pub(crate) fn select_for(f: Features, aes: &[&[&str]]) -> Backend {
        let own = Features::all(&[VG_AES_EXPAND_KEY_AES_FEATURES, VG_AES_CTR32_AES_FEATURES]);
        if f.contains(own) && f.contains(Features::all(aes)) {
            Backend::Aes
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    pub(crate) fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

#[cfg(test)]
mod tests {
    use super::Backend;
    use crate::cpu::Features;

    /// The implementation chosen for each set of features: AES-NI needs
    /// AES-NI and SSSE3 (for counter mode), and everything the caller's
    /// functions need.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn select() {
        let aes = Features::of(&["aes", "ssse3"]);
        assert_eq!(Backend::select_for(aes, &[]), Backend::AesNi);
        assert_eq!(Backend::select_for(aes, &[&["aes"]]), Backend::AesNi);
        for f in [
            Features::of(&[]),
            Features::of(&["aes"]),
            Features::of(&["ssse3"]),
        ] {
            assert_eq!(Backend::select_for(f, &[]), Backend::Scalar);
        }
        assert_eq!(
            Backend::select_for(aes, &[&["aes"], &["pclmulqdq"]]),
            Backend::Scalar
        );
        let all = Features::of(&["aes", "pclmulqdq", "ssse3"]);
        assert_eq!(Backend::select_for(all, &[&["pclmulqdq"]]), Backend::AesNi);
    }

    /// The implementation chosen for each set of features.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn select() {
        let aes = Features::of(&["aes"]);
        assert_eq!(Backend::select_for(aes, &[]), Backend::Aes);
        assert_eq!(Backend::select_for(aes, &[&["aes"]]), Backend::Aes);
        assert_eq!(Backend::select_for(Features(0), &[]), Backend::Scalar);
        assert_eq!(Backend::select_for(aes, &[&["sha2"]]), Backend::Scalar);
    }

    /// The scalar implementation is the only one.
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    #[test]
    fn select() {
        assert_eq!(Backend::select(Features(0)), Backend::Scalar);
    }
}
