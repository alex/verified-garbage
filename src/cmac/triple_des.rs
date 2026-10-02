//! TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) with two- and three-key TDEA
//! (16- and 24-byte keys) and the full 8-byte MAC.
//!
//! Everything but buffering is the verified assembly for the target
//! architecture: `vg_cmac_triple_des_init` (contract
//! `VG.Spec.Cmac.tdesInitContract`) expands the key and derives the subkeys
//! `K1` and `K2`, `vg_cmac_triple_des_update`
//! (`VG.Spec.Cmac.tdesUpdateContract`) chains whole blocks, and
//! `vg_cmac_triple_des_finalize` (`VG.Spec.Cmac.tdesFinalizeContract`)
//! masks and pads the last block and encrypts it. This module only keeps the
//! last (possibly whole) block of what it has absorbed back for `finalize`.
//!
//! TDEA's 64-bit block makes it a poor choice for new protocols (see NIST
//! SP 800-131A): this is for interoperating with existing ones.

#![cfg(target_arch = "x86_64")]

use super::{InvalidKeyLength, InvalidMac};
use crate::arch::cmac_triple_des::{
    vg_cmac_triple_des_finalize, vg_cmac_triple_des_init, vg_cmac_triple_des_update,
};
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// An 8-byte block.
type Block = [u8; 8];

/// The working space of the CMAC functions, in 64-bit words.
const SCRATCH: usize = 80;

/// An incremental TDEA-CMAC computation.
///
/// A computation that has absorbed nothing yet can be cloned to MAC several
/// messages with the same key without expanding it again.
#[derive(Clone)]
pub struct TripleDesCmac {
    /// The three DES key schedules (384 bytes), then the subkeys `K1 ‖ K2`.
    key: [u8; 400],
    /// The chaining value: the encryption of the blocks absorbed so far,
    /// chained from the zero block.
    state: Block,
    /// What has been absorbed after them…
    buf: Block,
    /// …of which this many bytes: at most a block, and more than none once
    /// anything has been absorbed.
    buf_len: usize,
}

impl Drop for TripleDesCmac {
    /// Wipes the key schedule, the subkeys, the chaining value and the
    /// buffered data.
    fn drop(&mut self) {
        zeroize(&mut self.key);
        zeroize(&mut self.state);
        zeroize(&mut self.buf);
    }
}

impl TripleDesCmac {
    /// The size of the MAC, in bytes.
    pub const MAC_SIZE: usize = 8;

    /// Starts a TDEA-CMAC computation with `key`, which must be 16 bytes
    /// (two-key TDEA: `K1 ‖ K2`, with `K3 = K1`) or 24 bytes (three-key
    /// TDEA: `K1 ‖ K2 ‖ K3`) long. The DES keys' parity bits are ignored.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24) {
            return Err(InvalidKeyLength);
        }
        let mut c = TripleDesCmac {
            key: [0; 400],
            state: [0; 8],
            buf: [0; 8],
            buf_len: 0,
        };
        let mut scratch = MaybeUninit::<[u64; SCRATCH]>::uninit();
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16
        // or 24; `c.key` for reads and writes of 400 bytes and `scratch` of
        // 640. `c.key` is a field of a local and `scratch` a local, so
        // neither overlaps the other, `key` or the return address. The
        // scratch buffer is uninitialized: it is only working space, and the
        // contract's result does not depend on what it holds.
        unsafe {
            vg_cmac_triple_des_init(key.as_ptr(), key.len(), &mut c.key, scratch.as_mut_ptr())
        };
        Ok(c)
    }

    /// Chains the whole blocks `blocks` into the state.
    fn blocks(&mut self, blocks: &[Block]) {
        if blocks.is_empty() {
            return;
        }
        let mut scratch = MaybeUninit::<[u64; SCRATCH]>::uninit();
        let schedule = self.key.first_chunk::<384>().unwrap();
        // SAFETY: `schedule` holds the key schedule written by `new`; it is
        // valid for reads of 384 bytes, `self.state` for reads and writes of
        // 8, `blocks` for reads of `8 * blocks.len()` and `scratch`
        // (uninitialized working space, as in `new`) for reads and writes of
        // 640. `self.state` is a mutable borrow and `scratch` a local, so
        // neither overlaps another argument or the return address.
        unsafe {
            vg_cmac_triple_des_update(
                schedule,
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
            let n = data.len().min(8 - self.buf_len);
            self.buf[self.buf_len..self.buf_len + n].copy_from_slice(&data[..n]);
            self.buf_len += n;
            data = &data[n..];
            if data.is_empty() {
                return;
            }
            let buf = self.buf;
            self.blocks(&[buf]);
        }
        let (blocks, _) = data[..data.len() - 1].as_chunks::<8>();
        self.blocks(blocks);
        let rest = &data[8 * blocks.len()..];
        self.buf[..rest.len()].copy_from_slice(rest);
        self.buf_len = rest.len();
    }

    /// Returns the MAC of everything absorbed.
    pub fn finalize(mut self) -> [u8; 8] {
        let mut scratch = MaybeUninit::<[u64; SCRATCH]>::uninit();
        // SAFETY: `self.key` holds the key schedule and then its subkeys,
        // written by `new`; it is valid for reads of 400 bytes, `self.state`
        // for reads and writes of 8, `self.buf` for reads of `self.buf_len`
        // (at most 8) and `scratch` (uninitialized working space, as in
        // `new`) for reads and writes of 640. `self.state` is a mutable
        // borrow and `scratch` a local, so neither overlaps another argument
        // or the return address. The state is the chaining of the blocks
        // before the buffered ones, and the buffer holds at least a byte if
        // any were chained, as the contract's postcondition requires to give
        // the MAC.
        unsafe {
            vg_cmac_triple_des_finalize(
                &self.key,
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

    /// The MAC of `data` with `key`, which must be 16 or 24 bytes long.
    pub fn mac(key: &[u8], data: &[u8]) -> Result<[u8; 8], InvalidKeyLength> {
        let mut c = Self::new(key)?;
        c.update(data);
        Ok(c.finalize())
    }
}

#[cfg(test)]
mod tests {
    use super::TripleDesCmac;
    use crate::cmac::{InvalidKeyLength, InvalidMac};

    /// Keys of other lengths are rejected.
    #[test]
    fn key_lengths() {
        for len in [0, 8, 15, 17, 23, 25, 32] {
            assert_eq!(
                TripleDesCmac::new(&[0; 32][..len]).err(),
                Some(InvalidKeyLength)
            );
            assert_eq!(
                TripleDesCmac::mac(&[0; 32][..len], b"").err(),
                Some(InvalidKeyLength)
            );
        }
    }

    /// Absorbing a message in two pieces, split anywhere, gives the MAC of
    /// the whole, also from a clone of a computation that absorbed nothing.
    #[test]
    fn splits() {
        let key: [u8; 24] = core::array::from_fn(|i| 0x2b ^ i as u8);
        let msg: [u8; 30] = core::array::from_fn(|i| i as u8);
        let fresh = TripleDesCmac::new(&key).unwrap();
        for len in 0..=msg.len() {
            let mac = TripleDesCmac::mac(&key, &msg[..len]).unwrap();
            for split in 0..=len {
                let mut c = fresh.clone();
                c.update(&msg[..split]);
                c.update(&msg[split..len]);
                assert_eq!(c.finalize(), mac, "{split} of {len}");
            }
        }
    }

    /// A two-key TDEA key is the three-key one with `K3 = K1`.
    #[test]
    fn two_keys() {
        let key: [u8; 16] = core::array::from_fn(|i| 0x51 ^ (7 * i) as u8);
        let three = [&key[..], &key[..8]].concat();
        for len in [0, 7, 8, 9, 24] {
            let msg = [0xa5; 24];
            assert_eq!(
                TripleDesCmac::mac(&key, &msg[..len]),
                TripleDesCmac::mac(&three, &msg[..len])
            );
        }
    }

    /// `verify` accepts the MAC, and nothing else: not a MAC with a bit
    /// flipped, nor a truncated one.
    #[test]
    fn verify() {
        let key = [0x3c; 16];
        let mac = TripleDesCmac::mac(&key, b"message").unwrap();
        let check = |m: &[u8]| {
            let mut c = TripleDesCmac::new(&key).unwrap();
            c.update(b"message");
            c.verify(m)
        };
        assert_eq!(check(&mac), Ok(()));
        for i in 0..8 {
            let mut bad = mac;
            bad[i] ^= 1;
            assert_eq!(check(&bad), Err(InvalidMac));
        }
        assert_eq!(check(&mac[..7]), Err(InvalidMac));
    }
}
