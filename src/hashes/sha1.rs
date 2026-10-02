//! SHA-1 (FIPS 180-4).
//!
//! SHA-1 is broken as a collision-resistant hash function: use it only where
//! an existing protocol or file format requires it.
//!
//! `vg_sha1_init`, `vg_sha1_update` and `vg_sha1_finalize` for the target
//! architecture (contracts `VG.Spec.Sha1.initContract`, `updateContract` and
//! `finalizeContract`) maintain a streaming state that represents the
//! message absorbed so far (`VG.Spec.Sha1.Repr`: the hash value of its whole
//! blocks, and its remaining bytes), and pad it and output the digest.
//!
//! On x86-64, CPUs with the SHA extensions (and SSSE3) run
//! `vg_sha1_update_shani` and `vg_sha1_finalize_shani` instead, which have
//! the same contracts and call `vg_sha1_compress_shani`. On AArch64, the
//! `sha2` feature group enables the `_sha2` variants using SHA1C/P/M/H and
//! SHA1SU0/SHA1SU1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::sha1::{
    VG_SHA1_FINALIZE_SHA2_FEATURES, VG_SHA1_UPDATE_SHA2_FEATURES, vg_sha1_finalize_sha2,
    vg_sha1_update_sha2,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::sha1::{
    VG_SHA1_FINALIZE_SHANI_FEATURES, VG_SHA1_UPDATE_SHANI_FEATURES, vg_sha1_finalize_shani,
    vg_sha1_update_shani,
};
use crate::arch::sha1::{vg_sha1_finalize, vg_sha1_init, vg_sha1_update};

super::streaming_hash!(
    /// An incremental SHA-1 computation.
    Sha1 {
        state: 84,
        scratch: 20,
        block: 64,
        output: 20,
        final_hash: 20,
        init: vg_sha1_init,
        backends: Sha1Backend {
            Scalar => (vg_sha1_update, vg_sha1_finalize),
            #[cfg(target_arch = "aarch64")]
            Sha2 if [VG_SHA1_UPDATE_SHA2_FEATURES, VG_SHA1_FINALIZE_SHA2_FEATURES] =>
                (vg_sha1_update_sha2, vg_sha1_finalize_sha2),
            #[cfg(target_arch = "x86_64")]
            ShaNi if [VG_SHA1_UPDATE_SHANI_FEATURES, VG_SHA1_FINALIZE_SHANI_FEATURES] =>
                (vg_sha1_update_shani, vg_sha1_finalize_shani),
        },
    }
);

#[cfg(test)]
mod tests {
    use super::{Sha1, Sha1Backend};
    use crate::cpu::{Features, detected};

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha1::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha1::default();
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
            let backend = Sha1Backend::select(Features(bits));
            #[cfg(target_arch = "x86_64")]
            assert_eq!(backend == Sha1Backend::ShaNi, bits & 0b11 == 0b11);
            #[cfg(target_arch = "aarch64")]
            {
                let expected = if Features(bits).contains(Features::of(&["sha2"])) {
                    Sha1Backend::Sha2
                } else {
                    Sha1Backend::Scalar
                };
                assert_eq!(backend, expected, "{bits:#b}");
            }
            #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
            assert_eq!(backend, Sha1Backend::Scalar);
        }
        assert_eq!(Sha1::new().backend, Sha1Backend::select(detected()));
    }

    /// The `HashFunction` implementation is the inherent functions.
    #[test]
    fn hash_function() {
        use crate::hashes::HashFunction;
        let msg = [0x5a; 300];
        let mut h = <Sha1 as HashFunction>::new();
        HashFunction::update(&mut h, &msg[..100]);
        HashFunction::update(&mut h, &msg[100..]);
        assert_eq!(HashFunction::finalize(h), Sha1::digest(&msg));
        assert_eq!(<Sha1 as HashFunction>::digest(&msg), Sha1::digest(&msg));
        assert_eq!(<Sha1 as HashFunction>::OUTPUT_SIZE, 20);
        assert_eq!(<Sha1 as HashFunction>::BLOCK_SIZE, 64);
    }
}
