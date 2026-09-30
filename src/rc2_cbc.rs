//! RC2-CBC (RFC 2268), without padding.
//!
//! Key expansion and CBC encryption/decryption use the verified x86-64
//! primitives (`VG.Spec.Rc2.expandKeyContract` and the CBC contracts).
//! This wrapper validates parameters and buffers partial blocks between
//! updates. Finalization rejects a trailing partial block.

#![cfg(all(any(target_arch = "x86_64", target_arch = "arm"), feature = "alloc"))]

use alloc::vec::Vec;

use crate::arch::rc2::{vg_rc2_cbc_decrypt, vg_rc2_cbc_encrypt, vg_rc2_expand_key};
use crate::mlkem768::zeroize;

/// Whether to encrypt plaintext or decrypt ciphertext.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    /// Encrypt plaintext.
    Encrypt,
    /// Decrypt ciphertext.
    Decrypt,
}

/// Why RC2-CBC initialization or finalization failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key length is outside 1..=128 bytes.
    InvalidKeyLength,
    /// The effective key size is outside 1..=1024 bits.
    InvalidEffectiveBits,
    /// The IV is not eight bytes long.
    InvalidIvLength,
    /// The total input length is not a multiple of eight bytes.
    IncompleteBlock,
}

/// A streaming RC2-CBC encryptor or decryptor, without padding.
pub struct Rc2Cbc {
    schedule: [u8; 128],
    iv: [u8; 8],
    pending: [u8; 8],
    pending_len: usize,
    direction: Direction,
}

impl Rc2Cbc {
    /// Initializes CBC, using the supplied key's bit length as the effective
    /// key size. Keys may contain 1..=128 bytes; the IV must contain eight.
    pub fn init(key: &[u8], iv: &[u8], direction: Direction) -> Result<Self, Error> {
        Self::init_with_effective_bits(key, iv, direction, key.len().saturating_mul(8))
    }

    /// Initializes CBC with an explicit effective key size of 1..=1024 bits,
    /// independently of the supplied key's length of 1..=128 bytes.
    pub fn init_with_effective_bits(
        key: &[u8],
        iv: &[u8],
        direction: Direction,
        effective_bits: usize,
    ) -> Result<Self, Error> {
        if !(1..=128).contains(&key.len()) {
            return Err(Error::InvalidKeyLength);
        }
        if !(1..=1024).contains(&effective_bits) {
            return Err(Error::InvalidEffectiveBits);
        }
        let iv: [u8; 8] = iv.try_into().map_err(|_| Error::InvalidIvLength)?;
        let mut schedule = [0; 128];
        let mut scratch = [0u64; 64];
        // SAFETY: validated key length and effective bits; key, schedule,
        // and scratch are valid, separate objects with the required sizes.
        unsafe {
            vg_rc2_expand_key(
                key.as_ptr(),
                key.len(),
                effective_bits,
                &mut schedule,
                &mut scratch,
            );
        }
        zeroize(&mut scratch);
        Ok(Self {
            schedule,
            iv,
            pending: [0; 8],
            pending_len: 0,
            direction,
        })
    }

    /// Processes all complete blocks and returns their output. Retains up
    /// to seven trailing bytes for the next update; empty updates emit no
    /// bytes and preserve the current chaining value and pending input.
    pub fn update(&mut self, data: &[u8]) -> Vec<u8> {
        let mut output = Vec::with_capacity(self.pending_len + data.len());
        output.extend_from_slice(&self.pending[..self.pending_len]);
        output.extend_from_slice(data);
        let complete = output.len() / 8 * 8;
        self.pending_len = output.len() - complete;
        self.pending[..self.pending_len].copy_from_slice(&output[complete..]);
        output.truncate(complete);
        let mut scratch = [0u64; 64];
        // SAFETY: output contains complete eight-byte blocks, including
        // zero blocks. Its allocation, the schedule, IV, and scratch are
        // separate, valid buffers and do not overlap the callee's stack.
        unsafe {
            match self.direction {
                Direction::Encrypt => vg_rc2_cbc_encrypt(
                    &self.schedule,
                    &mut self.iv,
                    output.as_mut_ptr().cast(),
                    complete / 8,
                    &mut scratch,
                ),
                Direction::Decrypt => vg_rc2_cbc_decrypt(
                    &self.schedule,
                    &mut self.iv,
                    output.as_mut_ptr().cast(),
                    complete / 8,
                    &mut scratch,
                ),
            }
        }
        zeroize(&mut scratch);
        output
    }

    /// Consumes the context. Returns no bytes on success, or
    /// [`Error::IncompleteBlock`] if any partial block remains. Padding is
    /// neither added nor removed.
    pub fn finalize(self) -> Result<Vec<u8>, Error> {
        if self.pending_len == 0 {
            Ok(Vec::new())
        } else {
            Err(Error::IncompleteBlock)
        }
    }
}

impl Drop for Rc2Cbc {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
        zeroize(&mut self.iv);
        zeroize(&mut self.pending);
    }
}
