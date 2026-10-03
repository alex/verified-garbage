//! SHA-512 (FIPS 180-4).
//!
//! `vg_sha512_init`, `vg_sha512_update` and `vg_sha512_finalize` for the
//! target architecture (contracts `VG.Spec.Sha512.initContract`,
//! `updateContract` and `finalizeContract`) maintain a streaming state that
//! represents the message absorbed so far (`VG.Spec.Sha512.Repr`: the hash
//! value of its whole blocks, from the function's initial hash value, and its
//! remaining bytes), and pad it and output the digest. SHA-384, SHA-512/224
//! and SHA-512/256 share that state and these `update` and `finalize`, and
//! differ only in their initial hash value and in how much of the final hash
//! value is their digest (see `super::sha384`, `super::sha512_224` and
//! `super::sha512_256`).
//!
//! On x86-64, CPUs with the SHA512 extension (and AVX2) run
//! `vg_sha512_update_shani` and `vg_sha512_finalize_shani` instead, which have
//! the same contracts and call `vg_sha512_compress_shani`; CPUs without it but
//! with AVX2, BMI1 and BMI2 run `vg_sha512_update_avx2` and
//! `vg_sha512_finalize_avx2`, which call `vg_sha512_compress_avx2`.
//!
//! On AArch64, Rust's `sha3` feature enables the FEAT_SHA512 backend.
//! Dispatch follows the generated feature requirements.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
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
use crate::arch::sha512::{vg_sha512_finalize, vg_sha512_init, vg_sha512_update};

super::streaming_hash!(
    /// An incremental SHA-512 computation (FIPS 180-4 §6.4).
    Sha512 {
        state: 192,
        scratch: 172,
        block: 128,
        output: 64,
        final_hash: 64,
        init: vg_sha512_init,
        backends: Sha512Backend {
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
    use super::{Sha512, Sha512Backend};
    use crate::cpu::{Features, detected};

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 400] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha512::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha512::default();
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
            let backend = Sha512Backend::select(Features(bits));
            #[cfg(target_arch = "x86_64")]
            {
                // AVX, AVX2 and SHA512; AVX, AVX2, BMI1 and BMI2.
                let shani = bits & 0b10_0011_0000 == 0b10_0011_0000;
                let avx2 = bits & 0b1111_0000 == 0b1111_0000;
                let expected = if shani {
                    Sha512Backend::ShaNi
                } else if avx2 {
                    Sha512Backend::Avx2
                } else {
                    Sha512Backend::Scalar
                };
                assert_eq!(backend, expected, "{bits:#b}");
            }
            #[cfg(target_arch = "aarch64")]
            {
                let expected = if Features(bits).contains(Features::of(&["sha3"])) {
                    Sha512Backend::Sha3
                } else {
                    Sha512Backend::Scalar
                };
                assert_eq!(backend, expected, "{bits:#b}");
            }
            #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
            assert_eq!(backend, Sha512Backend::Scalar);
        }
        assert_eq!(Sha512::new().backend, Sha512Backend::select(detected()));
    }

    /// The `HashFunction` implementation is the inherent functions.
    #[test]
    fn hash_function() {
        use crate::hashes::HashFunction;
        let msg = [0x5a; 300];
        let mut h = <Sha512 as HashFunction>::new();
        HashFunction::update(&mut h, &msg[..100]);
        HashFunction::update(&mut h, &msg[100..]);
        assert_eq!(HashFunction::finalize(h), Sha512::digest(&msg));
        assert_eq!(<Sha512 as HashFunction>::digest(&msg), Sha512::digest(&msg));
        assert_eq!(
            (
                <Sha512 as HashFunction>::OUTPUT_SIZE,
                <Sha512 as HashFunction>::BLOCK_SIZE
            ),
            (64, 128)
        );
    }
}
