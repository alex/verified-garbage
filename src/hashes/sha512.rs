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

#[cfg(target_arch = "aarch64")]
use crate::asm::aarch64::sha512::{
    vg_sha384_init, vg_sha512_224_init, vg_sha512_256_init, vg_sha512_finalize, vg_sha512_init,
    vg_sha512_update,
};
#[cfg(target_arch = "arm")]
use crate::asm::arm::sha512::{
    vg_sha384_init, vg_sha512_224_init, vg_sha512_256_init, vg_sha512_finalize, vg_sha512_init,
    vg_sha512_update,
};
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::sha512::{
    vg_sha384_init, vg_sha512_224_init, vg_sha512_256_init, vg_sha512_finalize, vg_sha512_init,
    vg_sha512_update,
};

super::streaming_hash!(
    /// An incremental SHA-384 computation (FIPS 180-4 §6.5).
    Sha384 {
        state: 192,
        scratch: 34,
        block: 128,
        output: 48,
        final_hash: 64,
        init: vg_sha384_init,
        backends: Sha384Backend {
            Scalar => (vg_sha512_update, vg_sha512_finalize),
        },
    }
);
super::streaming_hash!(
    /// An incremental SHA-512 computation (FIPS 180-4 §6.4).
    Sha512 {
        state: 192,
        scratch: 34,
        block: 128,
        output: 64,
        final_hash: 64,
        init: vg_sha512_init,
        backends: Sha512Backend {
            Scalar => (vg_sha512_update, vg_sha512_finalize),
        },
    }
);
super::streaming_hash!(
    /// An incremental SHA-512/224 computation (FIPS 180-4 §6.6).
    Sha512_224 {
        state: 192,
        scratch: 34,
        block: 128,
        output: 28,
        final_hash: 64,
        init: vg_sha512_224_init,
        backends: Sha512_224Backend {
            Scalar => (vg_sha512_update, vg_sha512_finalize),
        },
    }
);
super::streaming_hash!(
    /// An incremental SHA-512/256 computation (FIPS 180-4 §6.7).
    Sha512_256 {
        state: 192,
        scratch: 34,
        block: 128,
        output: 32,
        final_hash: 64,
        init: vg_sha512_256_init,
        backends: Sha512_256Backend {
            Scalar => (vg_sha512_update, vg_sha512_finalize),
        },
    }
);

#[cfg(test)]
mod tests {
    use super::{Sha384, Sha512, Sha512_224, Sha512_256};

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
