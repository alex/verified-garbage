//! SHA-256 (FIPS 180-4).
//!
//! `vg_sha256_init`, `vg_sha256_update` and `vg_sha256_finalize` for the
//! target architecture (contracts `VG.Spec.Sha256.initX86_64`,
//! `updateX86_64`, `finalizeX86_64` and their AArch64, 32-bit ARM and x86
//! counterparts) maintain a streaming state that represents the message
//! absorbed so far (`VG.Spec.Sha256.Repr`: the hash value of its whole
//! blocks, and its remaining bytes), and pad it and output the digest.

#[cfg(target_arch = "aarch64")]
use crate::asm::aarch64::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};
#[cfg(target_arch = "arm")]
use crate::asm::arm::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};
#[cfg(target_arch = "x86")]
use crate::asm::x86::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};

super::streaming_hash!(
    /// An incremental SHA-256 computation.
    Sha256 {
        state: 96,
        scratch: 20,
        block: 64,
        output: 32,
        final_hash: 32,
        init: vg_sha256_init,
        update: vg_sha256_update,
        finalize: vg_sha256_finalize,
    }
);

#[cfg(test)]
mod tests {
    use super::Sha256;

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha256::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha256::default();
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
