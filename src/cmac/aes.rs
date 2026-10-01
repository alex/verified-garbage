//! AES-CMAC (NIST SP 800-38B, RFC 4493) with 128-, 192- and 256-bit AES
//! keys and the full 16-byte MAC.
//!
//! Everything but buffering is the verified assembly for the target
//! architecture: `vg_aes_expand_key` (contract
//! `VG.Spec.Aes.expandKeyContract`) expands the key, `vg_cmac_aes_subkeys`
//! (`VG.Spec.Cmac.aesSubkeysContract`) derives the subkeys `K1` and `K2`,
//! `vg_cmac_aes_update` (`VG.Spec.Cmac.aesUpdateContract`) chains whole
//! blocks, and `vg_cmac_aes_finalize` (`VG.Spec.Cmac.aesFinalizeContract`)
//! masks and pads the last block and encrypts it. This module only keeps the
//! last (possibly whole) block of what it has absorbed back for `finalize`.
//!
//! On x86-64, CPUs with AES-NI and SSSE3 run `vg_aes_expand_key_aesni` and
//! the `_aesni` CMAC functions instead, which have the same contracts: the
//! same verified CMAC code, calling `vg_aes_ctr32_aesni` rather than
//! `vg_aes_ctr32` to encrypt each block. On AArch64, CPUs with the AES
//! extension run `vg_aes_expand_key_aes` and the `_aes` CMAC functions,
//! calling `vg_aes_ctr32_aes`. ARMv7 and x86 have only the scalar
//! implementation.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use super::{InvalidKeyLength, InvalidMac};
use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::{VG_AES_EXPAND_KEY_AES_FEATURES, vg_aes_expand_key_aes};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes::{VG_AES_EXPAND_KEY_AESNI_FEATURES, vg_aes_expand_key_aesni};
#[cfg(target_arch = "aarch64")]
use crate::arch::cmac_aes::{
    VG_CMAC_AES_FINALIZE_AES_FEATURES, VG_CMAC_AES_SUBKEYS_AES_FEATURES,
    VG_CMAC_AES_UPDATE_AES_FEATURES, vg_cmac_aes_finalize_aes, vg_cmac_aes_subkeys_aes,
    vg_cmac_aes_update_aes,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::cmac_aes::{
    VG_CMAC_AES_FINALIZE_AESNI_FEATURES, VG_CMAC_AES_SUBKEYS_AESNI_FEATURES,
    VG_CMAC_AES_UPDATE_AESNI_FEATURES, vg_cmac_aes_finalize_aesni, vg_cmac_aes_subkeys_aesni,
    vg_cmac_aes_update_aesni,
};
use crate::arch::cmac_aes::{vg_cmac_aes_finalize, vg_cmac_aes_subkeys, vg_cmac_aes_update};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// A 16-byte block.
type Block = [u8; 16];

/// The working space of the CMAC functions, in 64-bit words.
const SCRATCH: usize = 272;

/// The implementations of the primitives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// Constant-time scalar code, for the target's baseline ISA.
    Scalar,
    /// AES-NI.
    #[cfg(target_arch = "x86_64")]
    AesNi,
    /// The AES extension.
    #[cfg(target_arch = "aarch64")]
    ArmCrypto,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Backend {
        if f.contains(Features::all(&[
            VG_AES_EXPAND_KEY_AESNI_FEATURES,
            VG_CMAC_AES_SUBKEYS_AESNI_FEATURES,
            VG_CMAC_AES_UPDATE_AESNI_FEATURES,
            VG_CMAC_AES_FINALIZE_AESNI_FEATURES,
        ])) {
            Backend::AesNi
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "aarch64")]
    fn select(f: Features) -> Backend {
        if f.contains(Features::all(&[
            VG_AES_EXPAND_KEY_AES_FEATURES,
            VG_CMAC_AES_SUBKEYS_AES_FEATURES,
            VG_CMAC_AES_UPDATE_AES_FEATURES,
            VG_CMAC_AES_FINALIZE_AES_FEATURES,
        ])) {
            Backend::ArmCrypto
        } else {
            Backend::Scalar
        }
    }

    /// The only implementation there is.
    #[cfg(any(target_arch = "arm", target_arch = "x86"))]
    fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

/// An incremental AES-CMAC computation.
///
/// A computation that has absorbed nothing yet can be cloned to MAC several
/// messages with the same key without expanding it again.
#[derive(Clone)]
pub struct AesCmac {
    /// The AES key schedule (240 bytes), then the subkeys `K1 ‖ K2`.
    key: [u8; 272],
    rounds: usize,
    backend: Backend,
    /// The chaining value: the encryption of the blocks absorbed so far,
    /// chained from the zero block.
    state: Block,
    /// What has been absorbed after them…
    buf: Block,
    /// …of which this many bytes: at most a block, and more than none once
    /// anything has been absorbed.
    buf_len: usize,
}

impl Drop for AesCmac {
    /// Wipes the key schedule, the subkeys, the chaining value and the
    /// buffered data.
    fn drop(&mut self) {
        zeroize(&mut self.key);
        zeroize(&mut self.state);
        zeroize(&mut self.buf);
    }
}

impl AesCmac {
    /// The size of the MAC, in bytes.
    pub const MAC_SIZE: usize = 16;

    /// Starts an AES-CMAC computation with `key`, which must be 16, 24 or 32
    /// bytes long (AES-128, AES-192 or AES-256).
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut c = AesCmac {
            key: [0; 272],
            rounds: key.len() / 4 + 6,
            backend: Backend::select(detected()),
            state: [0; 16],
            buf: [0; 16],
            buf_len: 0,
        };
        let (schedule, subkeys) = c.key.split_first_chunk_mut::<240>().unwrap();
        let subkeys: &mut [u8; 32] = subkeys.try_into().unwrap();
        let mut expand_scratch = MaybeUninit::<[u64; 64]>::uninit();
        let mut scratch = MaybeUninit::<[u64; SCRATCH]>::uninit();
        let (k, rounds) = (key.as_ptr(), c.rounds);
        let (e, s) = (expand_scratch.as_mut_ptr(), scratch.as_mut_ptr());
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `schedule` for reads and writes of 240 bytes, `subkeys`
        // of 32, `expand_scratch` of 512 and `scratch` of 2176. `schedule`
        // and `subkeys` are disjoint parts of `c.key`, and the scratch
        // buffers locals, so no two overlap each other, `key` or the return
        // address. Key expansion leaves the schedule for `rounds` (10, 12 or
        // 14) rounds in `schedule`, which the subkey derivation reads. The
        // CPU has the features of the implementation selected. The scratch
        // buffers are uninitialized: they are only working space, and
        // neither contract's result depends on what they hold.
        unsafe {
            match c.backend {
                Backend::Scalar => {
                    vg_aes_expand_key(k, key.len(), schedule, e);
                    vg_cmac_aes_subkeys(schedule, rounds, subkeys, s);
                }
                #[cfg(target_arch = "x86_64")]
                Backend::AesNi => {
                    vg_aes_expand_key_aesni(k, key.len(), schedule, e);
                    vg_cmac_aes_subkeys_aesni(schedule, rounds, subkeys, s);
                }
                #[cfg(target_arch = "aarch64")]
                Backend::ArmCrypto => {
                    vg_aes_expand_key_aes(k, key.len(), schedule, e);
                    vg_cmac_aes_subkeys_aes(schedule, rounds, subkeys, s);
                }
            }
        }
        Ok(c)
    }

    /// Chains the whole blocks `blocks` into the state.
    fn blocks(&mut self, blocks: &[Block]) {
        if blocks.is_empty() {
            return;
        }
        let mut scratch = MaybeUninit::<[u64; SCRATCH]>::uninit();
        let f = match self.backend {
            Backend::Scalar => vg_cmac_aes_update,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => vg_cmac_aes_update_aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::ArmCrypto => vg_cmac_aes_update_aes,
        };
        let schedule = self.key.first_chunk::<240>().unwrap();
        // SAFETY: `schedule` holds the key schedule for `self.rounds` (10,
        // 12 or 14) rounds, written by key expansion (every implementation
        // writes the same one); it is valid for reads of 240 bytes,
        // `self.state` for reads and writes of 16, `blocks` for reads of
        // `16 * blocks.len()` and `scratch` (uninitialized working space, as
        // in `new`) for reads and writes of 2176. `self.state` is a mutable
        // borrow and `scratch` a local, so neither overlaps another argument
        // or the return address. The CPU has the features of the
        // implementation selected.
        unsafe {
            f(
                schedule,
                self.rounds,
                &mut self.state,
                blocks.as_ptr(),
                blocks.len(),
                scratch.as_mut_ptr(),
            )
        };
    }

    /// Absorbs `data`.
    pub fn update(&mut self, mut data: &[u8]) {
        if data.is_empty() {
            return;
        }
        // Fill the buffer, and chain it only if more data follows: the last
        // block, even a whole one, is `finalize`'s.
        if self.buf_len > 0 {
            let n = data.len().min(16 - self.buf_len);
            self.buf[self.buf_len..self.buf_len + n].copy_from_slice(&data[..n]);
            self.buf_len += n;
            data = &data[n..];
            if data.is_empty() {
                return;
            }
            let buf = self.buf;
            self.blocks(&[buf]);
        }
        let (blocks, _) = data[..data.len() - 1].as_chunks::<16>();
        self.blocks(blocks);
        let rest = &data[16 * blocks.len()..];
        self.buf[..rest.len()].copy_from_slice(rest);
        self.buf_len = rest.len();
    }

    /// Returns the MAC of everything absorbed.
    pub fn finalize(mut self) -> [u8; 16] {
        let mut scratch = MaybeUninit::<[u64; SCRATCH]>::uninit();
        let f = match self.backend {
            Backend::Scalar => vg_cmac_aes_finalize,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => vg_cmac_aes_finalize_aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::ArmCrypto => vg_cmac_aes_finalize_aes,
        };
        // SAFETY: `self.key` holds the key schedule for `self.rounds` (10, 12
        // or 14) rounds and then its subkeys, written by `new`; it is valid
        // for reads of 272 bytes, `self.state` for reads and writes of 16,
        // `self.buf` for reads of `self.buf_len` (at most 16) and `scratch`
        // (uninitialized working space, as in `new`) for reads and writes of
        // 2176. `self.state` is a mutable borrow and `scratch` a local, so
        // neither overlaps another argument or the return address. The state
        // is the chaining of the blocks before the buffered ones, and the
        // buffer holds at least a byte if any were chained, as the contract's
        // postcondition requires to give the MAC. The CPU has the features
        // of the implementation selected.
        unsafe {
            f(
                &self.key,
                self.rounds,
                &mut self.state,
                self.buf.as_ptr(),
                self.buf_len,
                scratch.as_mut_ptr(),
            )
        };
        self.state
    }

    /// Checks that `mac` is the MAC of everything absorbed, in constant
    /// time: the time taken does not depend on where, or whether, `mac`
    /// differs from it (its length is public). `mac` must be the whole MAC,
    /// of [`MAC_SIZE`](Self::MAC_SIZE) bytes; a truncated one is rejected.
    pub fn verify(self, mac: &[u8]) -> Result<(), InvalidMac> {
        if crate::ct::eq(&self.finalize(), mac) {
            Ok(())
        } else {
            Err(InvalidMac)
        }
    }

    /// The MAC of `data` with `key`, which must be 16, 24 or 32 bytes long.
    pub fn mac(key: &[u8], data: &[u8]) -> Result<[u8; 16], InvalidKeyLength> {
        let mut c = Self::new(key)?;
        c.update(data);
        Ok(c.finalize())
    }
}

#[cfg(test)]
mod tests {
    use super::{AesCmac, Backend};
    use crate::cmac::InvalidKeyLength;
    use crate::cpu::Features;

    /// Keys of other lengths are rejected.
    #[test]
    fn key_lengths() {
        for len in [0, 15, 17, 23, 25, 31, 33, 64] {
            assert_eq!(AesCmac::new(&[0; 64][..len]).err(), Some(InvalidKeyLength));
            assert_eq!(
                AesCmac::mac(&[0; 64][..len], b"").err(),
                Some(InvalidKeyLength)
            );
        }
    }

    /// Absorbing a message in two pieces, split anywhere, gives the MAC of
    /// the whole, also from a clone of a computation that absorbed nothing.
    #[test]
    fn splits() {
        let key = [0x2b; 16];
        let msg: [u8; 50] = core::array::from_fn(|i| i as u8);
        let fresh = AesCmac::new(&key).unwrap();
        for len in 0..=msg.len() {
            let mac = AesCmac::mac(&key, &msg[..len]).unwrap();
            for split in 0..=len {
                let mut c = fresh.clone();
                c.update(&msg[..split]);
                c.update(&msg[split..len]);
                assert_eq!(c.finalize(), mac, "{split} of {len}");
            }
        }
    }

    /// Each implementation is selected exactly when the CPU has its
    /// features.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn select() {
        assert_eq!(Backend::select(Features::of(&[])), Backend::Scalar);
        assert_eq!(
            Backend::select(Features::of(&["aes", "ssse3"])),
            Backend::AesNi
        );
        assert_eq!(Backend::select(Features::of(&["aes"])), Backend::Scalar);
    }

    /// Each implementation is selected exactly when the CPU has its
    /// features.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn select() {
        assert_eq!(Backend::select(Features::of(&[])), Backend::Scalar);
        assert_eq!(Backend::select(Features::of(&["aes"])), Backend::ArmCrypto);
    }

    /// The scalar implementation is the only one.
    #[cfg(any(target_arch = "arm", target_arch = "x86"))]
    #[test]
    fn select() {
        assert_eq!(Backend::select(Features::of(&[])), Backend::Scalar);
    }
}
