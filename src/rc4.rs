//! Raw RC4 (ARCFOUR), with an incremental keystream and no initial discard.
//!
//! RC4 is obsolete and insecure; this module exists for legacy compatibility.
//! It provides no nonce or authentication. Initialization and in-place XOR
//! are the verified primitives (`VG.Spec.Rc4.initContract` and
//! `VG.Spec.Rc4.applyContract`). Secret indices never address memory: the
//! primitives scan the permutation at fixed addresses, with NEON register
//! tables on AArch64 and masked quadwords on x86-64. Only pointers, lengths
//! and the stream position modulo 256 may affect the leakage trace.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use core::mem::MaybeUninit;

use crate::arch::rc4::{vg_rc4_apply, vg_rc4_init};
use crate::zeroize::{zeroize, zeroize_raw};

/// Why RC4 initialization failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key length is outside 1..=256 bytes.
    InvalidKeyLength,
}

/// An incremental raw RC4 encryptor or decryptor.
pub struct Rc4 {
    /// The permutation and two indices. Initialization writes every byte
    /// on success; only verified primitives read this opaque context.
    ctx: MaybeUninit<[u8; 258]>,
}

impl Rc4 {
    /// Schedules a key of 1..=256 bytes and starts at stream position zero.
    /// Longer keys are rejected rather than truncated. No bytes are discarded.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        let mut c = Self {
            ctx: MaybeUninit::uninit(),
        };
        let mut scratch = [0u64; 8];
        // SAFETY: the key is readable for its length, and the context and
        // scratch are writable for 258 and 64 bytes. Initialization reads
        // no context byte before writing it and checks the key length.
        // These distinct objects do not overlap or wrap around the address
        // space; the primitive uses only baseline instructions.
        let code =
            unsafe { vg_rc4_init(key.as_ptr(), key.len(), c.ctx.as_mut_ptr(), &mut scratch) };
        zeroize(&mut scratch);
        if code == 0 {
            Ok(c)
        } else {
            Err(Error::InvalidKeyLength)
        }
    }

    /// XORs the next stream bytes into `data`, encrypting or decrypting it.
    /// Updates consume exactly their input length; empty input preserves
    /// the context. The next call continues at the next stream byte.
    pub fn apply_keystream(&mut self, data: &mut [u8]) {
        let mut scratch = [0u64; 8];
        // SAFETY: successful initialization wrote the entire context.
        // The context, data and scratch are valid, separate objects of the
        // lengths passed, with no address-space wrapping. The target's
        // baseline includes every instruction used by the primitive.
        unsafe {
            vg_rc4_apply(
                self.ctx.as_mut_ptr(),
                data.as_mut_ptr(),
                data.len(),
                &mut scratch,
            );
        }
        zeroize(&mut scratch);
    }

    /// Consumes and wipes the context. Raw RC4 emits no final bytes or tag.
    pub fn finalize(self) {}
}

impl Drop for Rc4 {
    fn drop(&mut self) {
        // SAFETY: the context is writable for all 258 bytes, including
        // after failed initialization. It is a distinct Rust object that
        // does not overlap the callee's stack or wrap around the address space.
        unsafe { zeroize_raw(self.ctx.as_mut_ptr().cast::<u8>(), 258) };
    }
}
