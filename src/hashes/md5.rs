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

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

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
        },
    }
);

#[cfg(test)]
mod tests {
    use super::Md5;

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
}
