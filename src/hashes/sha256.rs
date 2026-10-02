//! SHA-256 (FIPS 180-4).
//!
//! `vg_sha256_init`, `vg_sha256_update` and `vg_sha256_finalize` for the
//! target architecture (contracts `VG.Spec.Sha256.initContract`,
//! `updateContract` and `finalizeContract`) maintain a streaming state that
//! represents the message absorbed so far (`VG.Spec.Sha256.Repr`: the hash
//! value of its whole blocks, and its remaining bytes), and pad it and output
//! the digest.
//!
//! On x86 and x86-64, CPUs with the SHA extensions (and SSSE3) run
//! `vg_sha256_update_shani` and `vg_sha256_finalize_shani` instead, which
//! have the same contracts and call `vg_sha256_compress_shani`; CPUs without
//! them on x86-64 but with AVX2, BMI1 and BMI2 run `vg_sha256_update_avx2` and
//! `vg_sha256_finalize_avx2`, which call `vg_sha256_compress_avx2`.
//! On AArch64, the `sha2` feature selects the `_sha2` streaming functions,
//! whose compression uses SHA256H/SHA256H2 and SHA256SU0/SHA256SU1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::sha256::{
    VG_SHA256_FINALIZE_AVX2_FEATURES, VG_SHA256_UPDATE_AVX2_FEATURES, vg_sha256_finalize_avx2,
    vg_sha256_update_avx2,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::sha256::{
    VG_SHA256_FINALIZE_SHA2_FEATURES, VG_SHA256_UPDATE_SHA2_FEATURES, vg_sha256_finalize_sha2,
    vg_sha256_update_sha2,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::sha256::{
    VG_SHA256_FINALIZE_SHANI_FEATURES, VG_SHA256_UPDATE_SHANI_FEATURES, vg_sha256_finalize_shani,
    vg_sha256_update_shani,
};
use crate::arch::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};

super::streaming_hash!(
    /// An incremental SHA-256 computation.
    Sha256 {
        state: 96,
        scratch: 76,
        block: 64,
        output: 32,
        final_hash: 32,
        init: vg_sha256_init,
        backends: Sha256Backend {
            Scalar => (vg_sha256_update, vg_sha256_finalize),
            #[cfg(target_arch = "aarch64")]
            Sha2 if [VG_SHA256_UPDATE_SHA2_FEATURES, VG_SHA256_FINALIZE_SHA2_FEATURES] =>
                (vg_sha256_update_sha2, vg_sha256_finalize_sha2),
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            ShaNi if [VG_SHA256_UPDATE_SHANI_FEATURES, VG_SHA256_FINALIZE_SHANI_FEATURES] =>
                (vg_sha256_update_shani, vg_sha256_finalize_shani),
            #[cfg(target_arch = "x86_64")]
            Avx2 if [VG_SHA256_UPDATE_AVX2_FEATURES, VG_SHA256_FINALIZE_AVX2_FEATURES] =>
                (vg_sha256_update_avx2, vg_sha256_finalize_avx2),
        },
    }
);

#[cfg(test)]
mod tests {
    use super::{Sha256, Sha256Backend};
    use crate::cpu::{Features, detected};

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha256::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha256::new();
                h.update(&msg[..split]);
                let copy = h.clone();
                h.update(&msg[split..len]);
                assert_eq!(h.finalize(), expected);
                let mut h = copy;
                for byte in &msg[split..len] {
                    h.update(core::slice::from_ref(byte));
                }
                assert_eq!(h.finalize(), expected);
            }
        }
    }

    /// The implementation chosen for each set of the features it depends on.
    #[test]
    fn select() {
        for bits in 0..(1 << crate::cpu::NAMES.len()) {
            let backend = Sha256Backend::select(Features(bits));
            #[cfg(target_arch = "x86_64")]
            {
                let shani = bits & 0b11 == 0b11;
                let avx2 = bits & 0b1111_0000 == 0b1111_0000;
                let expected = if shani {
                    Sha256Backend::ShaNi
                } else if avx2 {
                    Sha256Backend::Avx2
                } else {
                    Sha256Backend::Scalar
                };
                assert_eq!(backend, expected, "{bits:#b}");
            }
            #[cfg(target_arch = "aarch64")]
            {
                let expected = if Features(bits).contains(Features::of(&["sha2"])) {
                    Sha256Backend::Sha2
                } else {
                    Sha256Backend::Scalar
                };
                assert_eq!(backend, expected, "{bits:#b}");
            }
            #[cfg(target_arch = "x86")]
            {
                let expected = if Features(bits).contains(Features::of(&["sha", "ssse3"])) {
                    Sha256Backend::ShaNi
                } else {
                    Sha256Backend::Scalar
                };
                assert_eq!(backend, expected, "{bits:#b}");
            }
            #[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
            assert_eq!(backend, Sha256Backend::Scalar);
        }
        assert_eq!(Sha256::new().backend, Sha256Backend::select(detected()));
    }
}
