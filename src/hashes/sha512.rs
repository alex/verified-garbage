//! SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4).
//!
//! `vg_sha384_init`, `vg_sha512_init`, `vg_sha512_224_init` or
//! `vg_sha512_256_init`, then `vg_sha512_update` and `vg_sha512_finalize`
//! (contracts `VG.Spec.Sha512.initContract`, `updateContract` and
//! `finalizeContract`) maintain a streaming state that represents the message
//! absorbed so far (`VG.Spec.Sha512.Repr`: the hash value of its whole
//! blocks, from the function's initial hash value, and its remaining bytes),
//! and pad it and output the final hash value. The four functions share that
//! state and differ only in their initial hash value and in how much of the
//! final hash value is their digest.
//!
//! On x86-64, CPUs with the SHA512 extension (and AVX2) run
//! `vg_sha512_update_shani` and `vg_sha512_finalize_shani` instead, which have
//! the same contracts and call `vg_sha512_compress_shani`; CPUs without it but
//! with AVX2, BMI1 and BMI2 run `vg_sha512_update_avx2` and
//! `vg_sha512_finalize_avx2`, which call `vg_sha512_compress_avx2`.

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
use crate::arch::sha512::{
    vg_sha384_init, vg_sha512_224_init, vg_sha512_256_init, vg_sha512_finalize, vg_sha512_init,
    vg_sha512_update,
};

super::streaming_hash!(
    /// An incremental SHA-384 computation (FIPS 180-4 §6.5).
    Sha384 {
        state: 192,
        scratch: 172,
        block: 128,
        output: 48,
        final_hash: 64,
        init: vg_sha384_init,
        backends: Sha384Backend {
            Scalar => (vg_sha512_update, vg_sha512_finalize),
            #[cfg(target_arch = "x86_64")]
            ShaNi if [VG_SHA512_UPDATE_SHANI_FEATURES, VG_SHA512_FINALIZE_SHANI_FEATURES] =>
                (vg_sha512_update_shani, vg_sha512_finalize_shani),
            #[cfg(target_arch = "x86_64")]
            Avx2 if [VG_SHA512_UPDATE_AVX2_FEATURES, VG_SHA512_FINALIZE_AVX2_FEATURES] =>
                (vg_sha512_update_avx2, vg_sha512_finalize_avx2),
        },
    }
);
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
            #[cfg(target_arch = "x86_64")]
            ShaNi if [VG_SHA512_UPDATE_SHANI_FEATURES, VG_SHA512_FINALIZE_SHANI_FEATURES] =>
                (vg_sha512_update_shani, vg_sha512_finalize_shani),
            #[cfg(target_arch = "x86_64")]
            Avx2 if [VG_SHA512_UPDATE_AVX2_FEATURES, VG_SHA512_FINALIZE_AVX2_FEATURES] =>
                (vg_sha512_update_avx2, vg_sha512_finalize_avx2),
        },
    }
);
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
            #[cfg(target_arch = "x86_64")]
            ShaNi if [VG_SHA512_UPDATE_SHANI_FEATURES, VG_SHA512_FINALIZE_SHANI_FEATURES] =>
                (vg_sha512_update_shani, vg_sha512_finalize_shani),
            #[cfg(target_arch = "x86_64")]
            Avx2 if [VG_SHA512_UPDATE_AVX2_FEATURES, VG_SHA512_FINALIZE_AVX2_FEATURES] =>
                (vg_sha512_update_avx2, vg_sha512_finalize_avx2),
        },
    }
);
super::streaming_hash!(
    /// An incremental SHA-512/256 computation (FIPS 180-4 §6.7).
    Sha512_256 {
        state: 192,
        scratch: 172,
        block: 128,
        output: 32,
        final_hash: 64,
        init: vg_sha512_256_init,
        backends: Sha512_256Backend {
            Scalar => (vg_sha512_update, vg_sha512_finalize),
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
    use super::{
        Sha384, Sha384Backend, Sha512, Sha512_224, Sha512_224Backend, Sha512_256,
        Sha512_256Backend, Sha512Backend,
    };
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

    /// The implementation chosen for each set of the features it depends on,
    /// the same for the four functions.
    #[test]
    fn select() {
        for bits in 0..1024 {
            let f = Features(bits);
            let backend = Sha512Backend::select(f);
            #[cfg(target_arch = "x86_64")]
            {
                // AVX, AVX2 and SHA512; AVX, AVX2, BMI1 and BMI2.
                let shani = bits & 0b10_0011_0000 == 0b10_0011_0000;
                let avx2 = bits & 0b1111_0000 == 0b1111_0000;
                macro_rules! expected {
                    ($backend:ident) => {
                        if shani {
                            $backend::ShaNi
                        } else if avx2 {
                            $backend::Avx2
                        } else {
                            $backend::Scalar
                        }
                    };
                }
                assert_eq!(backend, expected!(Sha512Backend), "{bits:#b}");
                assert_eq!(Sha384Backend::select(f), expected!(Sha384Backend));
                assert_eq!(Sha512_224Backend::select(f), expected!(Sha512_224Backend));
                assert_eq!(Sha512_256Backend::select(f), expected!(Sha512_256Backend));
            }
            #[cfg(not(target_arch = "x86_64"))]
            {
                assert_eq!(backend, Sha512Backend::Scalar);
                assert_eq!(Sha384Backend::select(f), Sha384Backend::Scalar);
                assert_eq!(Sha512_224Backend::select(f), Sha512_224Backend::Scalar);
                assert_eq!(Sha512_256Backend::select(f), Sha512_256Backend::Scalar);
            }
        }
        assert_eq!(Sha512::new().backend, Sha512Backend::select(detected()));
        assert_eq!(Sha384::new().backend, Sha384Backend::select(detected()));
        assert_eq!(
            Sha512_224::new().backend,
            Sha512_224Backend::select(detected())
        );
        assert_eq!(
            Sha512_256::new().backend,
            Sha512_256Backend::select(detected())
        );
    }

    #[test]
    fn sizes() {
        assert_eq!(
            [
                Sha384::OUTPUT_SIZE,
                Sha512::OUTPUT_SIZE,
                Sha512_224::OUTPUT_SIZE,
                Sha512_256::OUTPUT_SIZE
            ],
            [48, 64, 28, 32]
        );
        assert_eq!(
            [
                Sha384::BLOCK_SIZE,
                Sha512::BLOCK_SIZE,
                Sha512_224::BLOCK_SIZE,
                Sha512_256::BLOCK_SIZE
            ],
            [128; 4]
        );
    }

    /// The `HashFunction` implementations are the inherent functions.
    #[test]
    fn hash_function() {
        use crate::hashes::HashFunction;
        fn check<H: HashFunction + Default>(digest: fn(&[u8]) -> H::Output) {
            let msg = [0x5a; 300];
            let mut h = <H as Default>::default();
            HashFunction::update(&mut h, &msg[..100]);
            HashFunction::update(&mut h, &msg[100..]);
            assert_eq!(h.finalize().as_ref(), digest(&msg).as_ref());
            assert_eq!(
                <H as HashFunction>::digest(&msg).as_ref(),
                digest(&msg).as_ref()
            );
            assert_eq!(digest(&msg).as_ref().len(), H::OUTPUT_SIZE);
            assert_eq!(H::BLOCK_SIZE, 128);
        }
        check::<Sha384>(Sha384::digest);
        check::<Sha512>(Sha512::digest);
        check::<Sha512_224>(Sha512_224::digest);
        check::<Sha512_256>(Sha512_256::digest);
    }
}
