//! Triple DES ECB (FIPS 46-3), without padding.
//!
//! Key expansion and ECB encryption/decryption use verified primitives.
//! This wrapper validates key lengths and buffers partial blocks between
//! updates. Finalization rejects a trailing partial block.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use alloc::vec::Vec;

use crate::arch::triple_des::{
    vg_triple_des_ecb_decrypt, vg_triple_des_ecb_encrypt, vg_triple_des_expand_key,
};
use crate::zeroize::zeroize;

/// Whether to encrypt plaintext or decrypt ciphertext.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    /// Encrypt plaintext.
    Encrypt,
    /// Decrypt ciphertext.
    Decrypt,
}

/// Why Triple DES ECB initialization or finalization failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16 or 24 bytes.
    InvalidKeyLength,
    /// The total input length is not a multiple of eight bytes.
    IncompleteBlock,
}

/// A streaming Triple DES ECB encryptor or decryptor, without padding.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored; weak and
/// repeated component keys are accepted.
pub struct TripleDesEcb {
    schedule: [u8; 384],
    pending: [u8; 8],
    pending_len: usize,
    direction: Direction,
}

impl TripleDesEcb {
    /// Initializes ECB with a 16- or 24-byte key and the chosen direction.
    pub fn init(key: &[u8], direction: Direction) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24) {
            return Err(Error::InvalidKeyLength);
        }
        let mut schedule = [0; 384];
        let mut scratch = [0u64; 64];
        // SAFETY: the key has a validated length; key, schedule and scratch
        // are separate valid buffers of the required sizes.
        unsafe {
            vg_triple_des_expand_key(key.as_ptr(), key.len(), &mut schedule, &mut scratch);
        }
        zeroize(&mut scratch);
        Ok(Self {
            schedule,
            pending: [0; 8],
            pending_len: 0,
            direction,
        })
    }

    /// Processes all complete eight-byte blocks and returns their output.
    /// Retains up to seven trailing bytes for the next update. Empty
    /// updates emit no bytes and preserve pending input.
    pub fn update(&mut self, data: &[u8]) -> Vec<u8> {
        let mut output = Vec::with_capacity(self.pending_len + data.len());
        output.extend_from_slice(&self.pending[..self.pending_len]);
        output.extend_from_slice(data);
        let complete = output.len() / 8 * 8;
        self.pending_len = output.len() - complete;
        self.pending[..self.pending_len].copy_from_slice(&output[complete..]);
        output.truncate(complete);
        let mut scratch = [0u64; 128];
        // SAFETY: output contains complete eight-byte blocks, including
        // zero blocks. Its allocation, schedule and scratch are separate
        // valid buffers, and do not overlap the callee's stack.
        unsafe {
            match self.direction {
                Direction::Encrypt => vg_triple_des_ecb_encrypt(
                    &self.schedule,
                    output.as_mut_ptr().cast(),
                    complete / 8,
                    &mut scratch,
                ),
                Direction::Decrypt => vg_triple_des_ecb_decrypt(
                    &self.schedule,
                    output.as_mut_ptr().cast(),
                    complete / 8,
                    &mut scratch,
                ),
            }
        }
        zeroize(&mut scratch);
        output
    }

    /// Consumes the context, returning no bytes on success. Returns
    /// [`Error::IncompleteBlock`] if any partial block remains. Padding
    /// is neither added nor removed.
    pub fn finalize(self) -> Result<Vec<u8>, Error> {
        if self.pending_len == 0 {
            Ok(Vec::new())
        } else {
            Err(Error::IncompleteBlock)
        }
    }
}

impl Drop for TripleDesEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
        zeroize(&mut self.pending);
    }
}
