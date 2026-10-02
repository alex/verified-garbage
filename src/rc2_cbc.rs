//! RC2-CBC (RFC 2268), without padding.
//!
//! Initialization and updates are the verified streaming primitives
//! (`VG.Spec.Rc2.cbcInitContract` and `VG.Spec.Rc2.cbcUpdateContract`),
//! which keep the key schedule, chaining value and pending partial block in
//! an opaque context. This wrapper keeps only the public parts: the
//! direction and the number of pending bytes. Finalization rejects a
//! trailing partial block.

#![cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "arm",
        target_arch = "aarch64",
        target_arch = "x86"
    ),
    feature = "alloc"
))]

use alloc::vec;
use alloc::vec::Vec;

pub use crate::aes_gcm::Direction;
use crate::arch::rc2::{vg_rc2_cbc_decrypt_update, vg_rc2_cbc_encrypt_update, vg_rc2_cbc_init};
use crate::zeroize::zeroize;

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
    /// The verified primitives' context: key schedule, chaining value and
    /// pending bytes.
    ctx: [u8; 144],
    pending_len: usize,
    direction: Direction,
}

impl Rc2Cbc {
    /// Initializes CBC, using the supplied key's bit length as the effective
    /// key size. Keys may contain 1..=128 bytes; the IV must contain eight.
    pub fn new(key: &[u8], iv: &[u8], direction: Direction) -> Result<Self, Error> {
        Self::new_with_effective_bits(key, iv, direction, key.len().saturating_mul(8))
    }

    /// Initializes CBC with an explicit effective key size of 1..=1024 bits,
    /// independently of the supplied key's length of 1..=128 bytes.
    pub fn new_with_effective_bits(
        key: &[u8],
        iv: &[u8],
        direction: Direction,
        effective_bits: usize,
    ) -> Result<Self, Error> {
        let mut ctx = Self {
            ctx: [0; 144],
            pending_len: 0,
            direction,
        };
        let mut scratch = [0u64; 72];
        // SAFETY: the key, IV, context and scratch are valid, separate
        // objects of the lengths passed; the primitive checks the lengths.
        let code = unsafe {
            vg_rc2_cbc_init(
                key.as_ptr(),
                key.len(),
                effective_bits,
                iv.as_ptr(),
                iv.len(),
                &mut ctx.ctx,
                &mut scratch,
            )
        };
        zeroize(&mut scratch);
        match code {
            0 => Ok(ctx),
            1 => Err(Error::InvalidKeyLength),
            2 => Err(Error::InvalidEffectiveBits),
            _ => Err(Error::InvalidIvLength),
        }
    }

    /// Processes all complete blocks and returns their output. Retains up
    /// to seven trailing bytes for the next update; empty updates emit no
    /// bytes and preserve the current chaining value and pending input.
    pub fn update(&mut self, data: &[u8]) -> Vec<u8> {
        let total = self.pending_len + data.len();
        let mut output = vec![0; total / 8 * 8];
        let mut scratch = [0u64; 72];
        let update = match self.direction {
            Direction::Encrypt => vg_rc2_cbc_encrypt_update,
            Direction::Decrypt => vg_rc2_cbc_decrypt_update,
        };
        // SAFETY: the context holds `pending_len` (less than 8) pending
        // bytes; `output` has room for exactly `(pending_len + len) / 8 * 8`
        // bytes; the context, data, output and scratch are valid, separate
        // objects.
        unsafe {
            update(
                &mut self.ctx,
                self.pending_len,
                data.as_ptr(),
                data.len(),
                output.as_mut_ptr(),
                output.len(),
                &mut scratch,
            );
        }
        zeroize(&mut scratch);
        self.pending_len = total % 8;
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
        zeroize(&mut self.ctx);
    }
}
