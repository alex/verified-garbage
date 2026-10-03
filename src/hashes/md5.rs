//! MD5 (RFC 1321).
//!
//! MD5 is broken as a collision-resistant hash function: use it only where
//! an existing protocol or file format requires it.
//!
//! `vg_md5_init`, `vg_md5_update` and `vg_md5_finalize` (contracts
//! `VG.Spec.Md5.initContract`, `updateContract` and `finalizeContract`)
//! maintain a streaming state that represents the message absorbed so far
//! (`VG.Spec.Md5.Repr`: the MD buffer after its whole blocks, and its
//! remaining bytes), and pad it and output the digest.
//!
//! On x86-64, CPUs with AVX512F and AVX512VL run `vg_md5_update_avx512` and
//! `vg_md5_finalize_avx512` instead, which have the same contracts and call
//! `vg_md5_compress_avx512`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::md5::{
    VG_MD5_FINALIZE_AVX512_FEATURES, VG_MD5_UPDATE_AVX512_FEATURES, vg_md5_finalize_avx512,
    vg_md5_update_avx512,
};
use crate::arch::md5::{vg_md5_finalize, vg_md5_init, vg_md5_update};

super::streaming_hash!(
    /// An incremental MD5 computation.
    Md5 {
        state: 80,
        scratch: 14,
        block: 64,
        output: 16,
        final_hash: 16,
        init: vg_md5_init,
        backends: Md5Backend {
            Scalar => (vg_md5_update, vg_md5_finalize),
            #[cfg(target_arch = "x86_64")]
            Avx512 if [VG_MD5_UPDATE_AVX512_FEATURES, VG_MD5_FINALIZE_AVX512_FEATURES] =>
                (vg_md5_update_avx512, vg_md5_finalize_avx512),
        },
    }
);

#[cfg(test)]
mod tests {
    use super::{Md5, Md5Backend};
    use crate::cpu::{Features, detected};

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Md5::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Md5::default();
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
            let backend = Md5Backend::select(Features(bits));
            #[cfg(target_arch = "x86_64")]
            {
                let expected =
                    if Features(bits).contains(Features::of(&["avx", "avx512f", "avx512vl"])) {
                        Md5Backend::Avx512
                    } else {
                        Md5Backend::Scalar
                    };
                assert_eq!(backend, expected, "{bits:#b}");
            }
            #[cfg(not(target_arch = "x86_64"))]
            assert_eq!(backend, Md5Backend::Scalar);
        }
        assert_eq!(Md5::new().backend, Md5Backend::select(detected()));
    }
}
