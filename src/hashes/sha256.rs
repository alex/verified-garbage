//! SHA-256 (FIPS 180-4).
//!
//! `vg_sha256_init`, `vg_sha256_update` and `vg_sha256_finalize` for the
//! target architecture (contracts `VG.Spec.Sha256.initContract`,
//! `updateContract` and `finalizeContract`) maintain a streaming state that
//! represents the message absorbed so far (`VG.Spec.Sha256.Repr`: the hash
//! value of its whole blocks, and its remaining bytes), and pad it and output
//! the digest.
//!
//! On x86-64, CPUs with the SHA extensions (and SSSE3) run
//! `vg_sha256_update_shani` and `vg_sha256_finalize_shani` instead, which
//! have the same contracts and call `vg_sha256_compress_shani`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "aarch64")]
use crate::asm::aarch64::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};
#[cfg(target_arch = "arm")]
use crate::asm::arm::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};
#[cfg(target_arch = "x86")]
use crate::asm::x86::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::sha256::{
    VG_SHA256_FINALIZE_SHANI_FEATURES, VG_SHA256_UPDATE_SHANI_FEATURES, vg_sha256_finalize,
    vg_sha256_finalize_shani, vg_sha256_init, vg_sha256_update, vg_sha256_update_shani,
};

super::streaming_hash!(
    /// An incremental SHA-256 computation.
    Sha256 {
        state: 96,
        scratch: 20,
        block: 64,
        output: 32,
        final_hash: 32,
        init: vg_sha256_init,
        backends: Sha256Backend {
            Scalar => (vg_sha256_update, vg_sha256_finalize),
            #[cfg(target_arch = "x86_64")]
            ShaNi if [VG_SHA256_UPDATE_SHANI_FEATURES, VG_SHA256_FINALIZE_SHANI_FEATURES] =>
                (vg_sha256_update_shani, vg_sha256_finalize_shani),
        },
    }
);

#[cfg(test)]
mod tests {
    use super::{Sha256, Sha256Backend};
    use crate::cpu::{Features, available};

    /// Masks that between them select every implementation this CPU can run.
    const MASKS: [u32; 2] = [u32::MAX, 0];

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries, with every
    /// implementation.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha256::digest(&msg[..len]);
            for (split, mask) in (0..=len).flat_map(|s| MASKS.map(|m| (s, m))) {
                let mut h = Sha256::__with_features(mask);
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
        for bits in 0..4 {
            let backend = Sha256Backend::select(Features(bits));
            #[cfg(target_arch = "x86_64")]
            assert_eq!(backend == Sha256Backend::ShaNi, bits == 0b11);
            #[cfg(not(target_arch = "x86_64"))]
            assert_eq!(backend, Sha256Backend::Scalar);
        }
        assert_eq!(Sha256::__with_features(0).backend, Sha256Backend::Scalar);
        assert_eq!(
            Sha256::new().backend,
            Sha256Backend::select(available(u32::MAX))
        );
    }
}
