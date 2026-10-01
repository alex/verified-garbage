//! SHA-224 (FIPS 180-4).
//!
//! SHA-224 is SHA-256 from another initial hash value, with its digest the
//! first 28 bytes of the final hash value. `vg_sha224_init` (contract
//! `VG.Spec.Sha256.init224Contract`) makes a SHA-256 streaming state
//! represent the empty message, hashed from SHA-224's initial hash value
//! (`VG.Spec.Sha256.ReprFrom`); SHA-256's `vg_sha256_update` and
//! `vg_sha256_finalize` (`updateContract` and `finalizeContract`, which hold
//! for any initial hash value) then absorb the message and output the final
//! hash value.
//!
//! The implementations of `update` and `finalize` are SHA-256's, chosen the
//! same way (see `super::sha256`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::sha256::{
    VG_SHA256_FINALIZE_AVX2_FEATURES, VG_SHA256_FINALIZE_SHANI_FEATURES,
    VG_SHA256_UPDATE_AVX2_FEATURES, VG_SHA256_UPDATE_SHANI_FEATURES, vg_sha256_finalize_avx2,
    vg_sha256_finalize_shani, vg_sha256_update_avx2, vg_sha256_update_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::sha256::{
    VG_SHA256_FINALIZE_SHA2_FEATURES, VG_SHA256_UPDATE_SHA2_FEATURES, vg_sha256_finalize_sha2,
    vg_sha256_update_sha2,
};
use crate::arch::sha256::{vg_sha224_init, vg_sha256_finalize, vg_sha256_update};

super::streaming_hash!(
    /// An incremental SHA-224 computation (FIPS 180-4 §6.3).
    Sha224 {
        state: 96,
        scratch: 76,
        block: 64,
        output: 28,
        final_hash: 32,
        init: vg_sha224_init,
        backends: Sha224Backend {
            Scalar => (vg_sha256_update, vg_sha256_finalize),
            #[cfg(target_arch = "aarch64")]
            Sha2 if [VG_SHA256_UPDATE_SHA2_FEATURES, VG_SHA256_FINALIZE_SHA2_FEATURES] =>
                (vg_sha256_update_sha2, vg_sha256_finalize_sha2),
            #[cfg(target_arch = "x86_64")]
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
    use super::{Sha224, Sha224Backend};
    use crate::cpu::{Features, detected};
    use crate::hashes::sha256::Sha256Backend;

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha224::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha224::default();
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

    /// The implementation chosen for each set of features is SHA-256's.
    #[test]
    fn select() {
        for bits in 0..(1 << crate::cpu::NAMES.len()) {
            let f = Features(bits);
            let expected = match Sha256Backend::select(f) {
                Sha256Backend::Scalar => Sha224Backend::Scalar,
                #[cfg(target_arch = "aarch64")]
                Sha256Backend::Sha2 => Sha224Backend::Sha2,
                #[cfg(target_arch = "x86_64")]
                Sha256Backend::ShaNi => Sha224Backend::ShaNi,
                #[cfg(target_arch = "x86_64")]
                Sha256Backend::Avx2 => Sha224Backend::Avx2,
            };
            assert_eq!(Sha224Backend::select(f), expected, "{bits:#b}");
        }
        assert_eq!(Sha224::new().backend, Sha224Backend::select(detected()));
    }

    /// The `HashFunction` implementation is the inherent functions.
    #[test]
    fn hash_function() {
        use crate::hashes::HashFunction;
        let msg = [0x5a; 300];
        let mut h = <Sha224 as HashFunction>::new();
        HashFunction::update(&mut h, &msg[..100]);
        HashFunction::update(&mut h, &msg[100..]);
        assert_eq!(HashFunction::finalize(h), Sha224::digest(&msg));
        assert_eq!(<Sha224 as HashFunction>::digest(&msg), Sha224::digest(&msg));
        assert_eq!(
            (
                <Sha224 as HashFunction>::OUTPUT_SIZE,
                <Sha224 as HashFunction>::BLOCK_SIZE
            ),
            (28, 64)
        );
    }
}
