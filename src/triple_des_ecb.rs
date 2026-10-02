//! Triple DES ECB (FIPS 46-3), in place and without padding.
//!
//! Key expansion and ECB encryption/decryption use verified primitives.
//! Each operation accepts complete eight-byte blocks, including empty input.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::triple_des::{
    vg_triple_des_ecb_decrypt, vg_triple_des_ecb_encrypt, vg_triple_des_expand_key,
};
use crate::zeroize::zeroize;

/// Why a Triple DES ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16 or 24 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of eight bytes.
    IncompleteBlock,
}

/// An expanded Triple DES key for ECB encryption and decryption.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored; weak and
/// repeated component keys are accepted. No padding is added or removed.
pub struct TripleDesEcb {
    schedule: [u8; 384],
}

impl TripleDesEcb {
    /// Expands a 16- or 24-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
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
        Ok(Self { schedule })
    }

    /// Encrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, true)
    }

    /// Decrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, false)
    }

    fn crypt(&self, buffer: &mut [u8], encrypt: bool) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(8) {
            return Err(Error::IncompleteBlock);
        }
        let mut scratch = [0u64; 128];
        // SAFETY: buffer contains complete eight-byte blocks, including zero
        // blocks. The buffer, schedule and scratch are separate valid objects
        // and do not overlap the callee's stack.
        unsafe {
            if encrypt {
                vg_triple_des_ecb_encrypt(
                    &self.schedule,
                    buffer.as_mut_ptr().cast(),
                    buffer.len() / 8,
                    &mut scratch,
                );
            } else {
                vg_triple_des_ecb_decrypt(
                    &self.schedule,
                    buffer.as_mut_ptr().cast(),
                    buffer.len() / 8,
                    &mut scratch,
                );
            }
        }
        zeroize(&mut scratch);
        Ok(())
    }
}

impl Drop for TripleDesEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
