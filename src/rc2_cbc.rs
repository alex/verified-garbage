//! RC2-CBC (RFC 2268), without padding: [`Rc2CbcEncryptor`] and
//! [`Rc2CbcDecryptor`].
//!
//! Initialization and updates are the verified streaming primitives
//! (`VG.Spec.Rc2.cbcInitContract` and `VG.Spec.Rc2.cbcUpdateContract`),
//! which keep the key schedule, chaining value and pending partial block in
//! an opaque context. This wrapper keeps only the number of pending bytes;
//! the direction is the type. Updates write the whole blocks they complete
//! to the caller's buffer, so nothing is allocated; finalization rejects a
//! trailing partial block.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "x86"
))]

use crate::arch::rc2::{vg_rc2_cbc_decrypt_update, vg_rc2_cbc_encrypt_update, vg_rc2_cbc_init};
use crate::zeroize::zeroize;

/// Why an RC2-CBC operation failed.
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
    /// The output buffer of an update is shorter than the bytes it would
    /// write ([`Rc2CbcEncryptor::output_len`],
    /// [`Rc2CbcDecryptor::output_len`]).
    OutputTooSmall,
}

/// A streaming RC2-CBC encryption (or, if `DECRYPT`, decryption), which
/// [`Rc2CbcEncryptor`] and [`Rc2CbcDecryptor`] wrap.
struct Cbc<const DECRYPT: bool> {
    /// The verified primitives' context: key schedule, chaining value and
    /// pending bytes.
    ctx: [u8; 144],
    pending_len: usize,
}

impl<const DECRYPT: bool> Cbc<DECRYPT> {
    /// Initializes CBC with an effective key size of `effective_bits`.
    fn new(key: &[u8], iv: &[u8], effective_bits: usize) -> Result<Self, Error> {
        let mut ctx = Self {
            ctx: [0; 144],
            pending_len: 0,
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

    /// The number of bytes an update with `input_len` bytes of input
    /// writes, saturating at `usize::MAX`.
    fn output_len(&self, input_len: usize) -> usize {
        self.pending_len
            .checked_add(input_len)
            .map_or(usize::MAX, |total| total / 8 * 8)
    }

    /// Processes the whole blocks of the pending bytes and `input` into the
    /// first bytes of `output`, keeps the rest pending, and returns how many
    /// bytes it wrote; changes nothing if `output` is too short.
    fn update(&mut self, input: &[u8], output: &mut [u8]) -> Result<usize, Error> {
        // No slice is `usize::MAX` bytes long, so an overflowing length
        // (`output_len` saturates) is too long for any `output`.
        let written = self.output_len(input.len());
        let output = output.get_mut(..written).ok_or(Error::OutputTooSmall)?;
        let mut scratch = [0u64; 72];
        let update = if DECRYPT {
            vg_rc2_cbc_decrypt_update
        } else {
            vg_rc2_cbc_encrypt_update
        };
        // SAFETY: the context holds `pending_len` (less than 8) pending
        // bytes; `output` is exactly `(pending_len + input.len()) / 8 * 8`
        // bytes long, as the contract requires; the context, input, output
        // and scratch are valid for their lengths and are separate objects
        // (`input` and `output` are distinct borrows, so they do not
        // overlap).
        unsafe {
            update(
                &mut self.ctx,
                self.pending_len,
                input.as_ptr(),
                input.len(),
                output.as_mut_ptr(),
                output.len(),
                &mut scratch,
            );
        }
        zeroize(&mut scratch);
        self.pending_len = (self.pending_len + input.len() % 8) % 8;
        Ok(written)
    }

    /// Fails if a partial block remains.
    fn finalize(self) -> Result<(), Error> {
        if self.pending_len == 0 {
            Ok(())
        } else {
            Err(Error::IncompleteBlock)
        }
    }
}

impl<const DECRYPT: bool> Drop for Cbc<DECRYPT> {
    fn drop(&mut self) {
        zeroize(&mut self.ctx);
    }
}

/// A streaming RC2-CBC encryptor, without padding.
pub struct Rc2CbcEncryptor {
    cbc: Cbc<false>,
}

impl Rc2CbcEncryptor {
    /// Initializes CBC, using the supplied key's bit length as the effective
    /// key size. Keys may contain 1..=128 bytes; the IV must contain eight.
    pub fn new(key: &[u8], iv: &[u8]) -> Result<Self, Error> {
        Self::new_with_effective_bits(key, iv, key.len().saturating_mul(8))
    }

    /// Initializes CBC with an explicit effective key size of 1..=1024 bits,
    /// independently of the supplied key's length of 1..=128 bytes.
    pub fn new_with_effective_bits(
        key: &[u8],
        iv: &[u8],
        effective_bits: usize,
    ) -> Result<Self, Error> {
        Ok(Self {
            cbc: Cbc::new(key, iv, effective_bits)?,
        })
    }

    /// The number of bytes the next [`update`](Self::update) with
    /// `input_len` bytes of input writes: the whole blocks of the pending
    /// bytes and the input, at most `input_len + 7` (saturating at
    /// `usize::MAX`, for lengths no slice has).
    pub fn output_len(&self, input_len: usize) -> usize {
        self.cbc.output_len(input_len)
    }

    /// Encrypts the whole blocks of the pending bytes and `input` into the
    /// first bytes of `output`, keeps the rest (at most seven bytes) pending
    /// for the next update, and returns how many bytes it wrote:
    /// [`output_len`](Self::output_len)`(input.len())`.
    ///
    /// `output` may be longer than that, and `input.len() + 7` bytes always
    /// suffice. If it is shorter, fails with [`Error::OutputTooSmall`],
    /// writing nothing and leaving the encryptor unchanged. An update that
    /// completes no block (an empty one, for example) writes nothing and
    /// keeps the chaining value.
    pub fn update(&mut self, input: &[u8], output: &mut [u8]) -> Result<usize, Error> {
        self.cbc.update(input, output)
    }

    /// Consumes the encryptor. Fails with [`Error::IncompleteBlock`] if a
    /// partial block is pending; padding is neither added nor removed.
    pub fn finalize(self) -> Result<(), Error> {
        self.cbc.finalize()
    }
}

/// A streaming RC2-CBC decryptor, without padding.
pub struct Rc2CbcDecryptor {
    cbc: Cbc<true>,
}

impl Rc2CbcDecryptor {
    /// Initializes CBC, using the supplied key's bit length as the effective
    /// key size. Keys may contain 1..=128 bytes; the IV must contain eight.
    pub fn new(key: &[u8], iv: &[u8]) -> Result<Self, Error> {
        Self::new_with_effective_bits(key, iv, key.len().saturating_mul(8))
    }

    /// Initializes CBC with an explicit effective key size of 1..=1024 bits,
    /// independently of the supplied key's length of 1..=128 bytes.
    pub fn new_with_effective_bits(
        key: &[u8],
        iv: &[u8],
        effective_bits: usize,
    ) -> Result<Self, Error> {
        Ok(Self {
            cbc: Cbc::new(key, iv, effective_bits)?,
        })
    }

    /// The number of bytes the next [`update`](Self::update) with
    /// `input_len` bytes of input writes: the whole blocks of the pending
    /// bytes and the input, at most `input_len + 7` (saturating at
    /// `usize::MAX`, for lengths no slice has).
    pub fn output_len(&self, input_len: usize) -> usize {
        self.cbc.output_len(input_len)
    }

    /// Decrypts the whole blocks of the pending bytes and `input` into the
    /// first bytes of `output`, keeps the rest (at most seven bytes) pending
    /// for the next update, and returns how many bytes it wrote:
    /// [`output_len`](Self::output_len)`(input.len())`.
    ///
    /// `output` may be longer than that, and `input.len() + 7` bytes always
    /// suffice. If it is shorter, fails with [`Error::OutputTooSmall`],
    /// writing nothing and leaving the decryptor unchanged. An update that
    /// completes no block (an empty one, for example) writes nothing and
    /// keeps the chaining value.
    pub fn update(&mut self, input: &[u8], output: &mut [u8]) -> Result<usize, Error> {
        self.cbc.update(input, output)
    }

    /// Consumes the decryptor. Fails with [`Error::IncompleteBlock`] if a
    /// partial block is pending; padding is neither added nor removed.
    pub fn finalize(self) -> Result<(), Error> {
        self.cbc.finalize()
    }
}
