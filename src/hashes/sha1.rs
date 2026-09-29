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

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

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
        },
    }
);

#[cfg(test)]
mod tests {
    use super::Sha1;

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
