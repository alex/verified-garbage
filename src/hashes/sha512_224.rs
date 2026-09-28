//! SHA-512/224 (FIPS 180-4).
//!
//! SHA-512/224 is SHA-512 from another initial hash value, with its digest the
//! first 28 bytes of the final hash value. `vg_sha512_224_init` (contract
//! `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.H0_512_224`) makes a SHA-512
//! streaming state represent the empty message, hashed from SHA-512/224's
//! initial hash value (`VG.Spec.Sha512.Repr`); SHA-512's `vg_sha512_update`
//! and `vg_sha512_finalize` (`updateContract` and `finalizeContract`, which
//! hold for any initial hash value) then absorb the message and output the
//! final hash value.
//!
//! The implementations of `update` and `finalize` are SHA-512's, chosen the
//! same way (see `super::sha512`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::sha512::{
    VG_SHA512_FINALIZE_AVX2_FEATURES, VG_SHA512_FINALIZE_SHANI_FEATURES,
    VG_SHA512_UPDATE_AVX2_FEATURES, VG_SHA512_UPDATE_SHANI_FEATURES, vg_sha512_finalize_avx2,
    vg_sha512_finalize_shani, vg_sha512_update_avx2, vg_sha512_update_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::sha512::{
    VG_SHA512_FINALIZE_SHA3_FEATURES, VG_SHA512_UPDATE_SHA3_FEATURES, vg_sha512_finalize_sha3,
    vg_sha512_update_sha3,
};
use crate::arch::sha512::{vg_sha512_224_init, vg_sha512_finalize, vg_sha512_update};

super::streaming_hash!(
    /// An incremental SHA-512/224 computation (FIPS 180-4 §6.6).
    Sha512_224 {
        state: 192,
        scratch: 172,
        block: 128,
        output: 28,
        final_hash: 64,
        init: vg_sha512_224_init,
        backends: Sha512_224Backend {
            Scalar => (vg_sha512_update, vg_sha512_finalize),
            #[cfg(target_arch = "aarch64")]
            Sha3 if [VG_SHA512_UPDATE_SHA3_FEATURES, VG_SHA512_FINALIZE_SHA3_FEATURES] =>
                (vg_sha512_update_sha3, vg_sha512_finalize_sha3),
            #[cfg(target_arch = "x86_64")]
            ShaNi if [VG_SHA512_UPDATE_SHANI_FEATURES, VG_SHA512_FINALIZE_SHANI_FEATURES] =>
                (vg_sha512_update_shani, vg_sha512_finalize_shani),
            #[cfg(target_arch = "x86_64")]
            Avx2 if [VG_SHA512_UPDATE_AVX2_FEATURES, VG_SHA512_FINALIZE_AVX2_FEATURES] =>
                (vg_sha512_update_avx2, vg_sha512_finalize_avx2),
        },
    }
);

#[cfg(test)]
mod tests {
    use super::{Sha512_224, Sha512_224Backend};
    use crate::cpu::{Features, detected};
    use crate::hashes::sha512::Sha512Backend;

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 400] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha512_224::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha512_224::default();
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

    /// The implementation chosen for each set of features is SHA-512's.
    #[test]
    fn select() {
        for bits in 0..(1 << crate::cpu::NAMES.len()) {
            let f = Features(bits);
            let expected = match Sha512Backend::select(f) {
                Sha512Backend::Scalar => Sha512_224Backend::Scalar,
                #[cfg(target_arch = "aarch64")]
                Sha512Backend::Sha3 => Sha512_224Backend::Sha3,
                #[cfg(target_arch = "x86_64")]
                Sha512Backend::ShaNi => Sha512_224Backend::ShaNi,
                #[cfg(target_arch = "x86_64")]
                Sha512Backend::Avx2 => Sha512_224Backend::Avx2,
            };
            assert_eq!(Sha512_224Backend::select(f), expected, "{bits:#b}");
        }
        assert_eq!(
            Sha512_224::new().backend,
            Sha512_224Backend::select(detected())
        );
    }

    /// The `HashFunction` implementation is the inherent functions.
    #[test]
    fn hash_function() {
        use crate::hashes::HashFunction;
        let msg = [0x5a; 300];
        let mut h = <Sha512_224 as HashFunction>::new();
        HashFunction::update(&mut h, &msg[..100]);
        HashFunction::update(&mut h, &msg[100..]);
        assert_eq!(HashFunction::finalize(h), Sha512_224::digest(&msg));
        assert_eq!(
            <Sha512_224 as HashFunction>::digest(&msg),
            Sha512_224::digest(&msg)
        );
        assert_eq!(
            (
                <Sha512_224 as HashFunction>::OUTPUT_SIZE,
                <Sha512_224 as HashFunction>::BLOCK_SIZE
            ),
            (28, 128)
        );
    }
}
