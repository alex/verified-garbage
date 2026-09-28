//! Poly1305 (RFC 8439 §2.5), a one-time authenticator.
//!
//! `vg_poly1305_init`, `vg_poly1305_blocks` and `vg_poly1305_finalize`
//! (contracts `VG.Spec.Poly1305.initContract`, `blocksContract` and
//! `finalizeContract`) maintain a streaming state that represents the key
//! and the whole 16-byte blocks of the message absorbed so far
//! (`VG.Spec.Poly1305.Repr`), and compute the tag of that message followed
//! by its last bytes. This module buffers the bytes of a partial block.
//!
//! A key must be used to authenticate only one message: the tags of two
//! messages under the same key reveal enough to forge others.

#![cfg(any(target_arch = "x86_64", target_arch = "arm"))]

#[cfg(target_arch = "arm")]
use crate::asm::arm::poly1305::{vg_poly1305_blocks, vg_poly1305_finalize, vg_poly1305_init};
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::poly1305::{vg_poly1305_blocks, vg_poly1305_finalize, vg_poly1305_init};

/// An incremental Poly1305 computation.
pub struct Poly1305 {
    /// The streaming state, representing the key and the message so far,
    /// except the bytes in `buf`.
    state: [u64; 16],
    /// The message's last bytes, not yet a whole block.
    buf: [u8; 16],
    /// How many bytes of `buf` are used (fewer than 16).
    used: usize,
}

impl Poly1305 {
    /// The size of a key, in bytes.
    pub const KEY_SIZE: usize = 32;
    /// The size of a tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Starts a computation with the one-time key `key`.
    pub fn new(key: &[u8; 32]) -> Self {
        let mut state = [0; 16];
        // SAFETY: `state` is valid for writes of 128 bytes and `key` for
        // reads of 32 bytes; they are distinct objects, so they do not overlap
        // each other or the return address, and neither wraps around the end
        // of the address space.
        unsafe { vg_poly1305_init(&mut state, key) };
        Poly1305 {
            state,
            buf: [0; 16],
            used: 0,
        }
    }

    /// Absorbs whole blocks.
    fn blocks(&mut self, blocks: &[[u8; 16]]) {
        // SAFETY: `self.state` is valid for reads and writes of 128 bytes and
        // `blocks` for reads of `16 * blocks.len()` bytes; they are distinct
        // objects, so they do not overlap each other or the return address,
        // and `blocks` does not wrap around the end of the address space.
        unsafe { vg_poly1305_blocks(&mut self.state, blocks.as_ptr(), blocks.len()) };
    }

    /// Absorbs `data`.
    pub fn update(&mut self, mut data: &[u8]) {
        if self.used > 0 {
            let n = data.len().min(16 - self.used);
            self.buf[self.used..self.used + n].copy_from_slice(&data[..n]);
            self.used += n;
            data = &data[n..];
            if self.used < 16 {
                return;
            }
            let block = self.buf;
            self.blocks(core::slice::from_ref(&block));
            self.used = 0;
        }
        let (blocks, rest) = data.as_chunks::<16>();
        self.blocks(blocks);
        self.buf[..rest.len()].copy_from_slice(rest);
        self.used = rest.len();
    }

    /// Returns the tag of everything absorbed.
    pub fn finalize(mut self) -> [u8; 16] {
        let mut tag = [0; 16];
        // SAFETY: `self.used` is less than 16; `self.state` is valid for reads
        // and writes of 128 bytes, `self.buf` for reads of `self.used` bytes
        // and `tag` for writes of 16 bytes; they are distinct objects, so they
        // do not overlap each other or the return address, and none wraps
        // around the end of the address space.
        unsafe { vg_poly1305_finalize(&mut self.state, self.buf.as_ptr(), self.used, &mut tag) };
        tag
    }

    /// The tag of `data` with the one-time key `key`.
    pub fn mac(key: &[u8; 32], data: &[u8]) -> [u8; 16] {
        let mut p = Self::new(key);
        p.update(data);
        p.finalize()
    }
}
