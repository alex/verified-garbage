//! Poly1305 (RFC 8439 §2.5), a one-time authenticator.
//!
//! Its whole computation is verified assembly: `vg_poly1305_init`,
//! `vg_poly1305_update` and `vg_poly1305_finalize` (contracts
//! `VG.Spec.Poly1305.initContract`, `updateContract` and `finalizeContract`)
//! maintain a streaming state that represents the key and the message
//! absorbed so far, with the message's last bytes that do not fill a block
//! buffered in it (`VG.Spec.Poly1305.Buffered`), and compute the tag. This
//! module only keeps that state together with the message length (modulo
//! 2⁶⁴), which the contracts take as an argument, and gives them working
//! space (`scratch`).
//!
//! A key must be used to authenticate only one message: the tags of two
//! messages under the same key reveal enough to forge others.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86"))]

#[cfg(target_arch = "aarch64")]
use crate::asm::aarch64::poly1305::{vg_poly1305_finalize, vg_poly1305_init, vg_poly1305_update};
#[cfg(target_arch = "x86")]
use crate::asm::x86::poly1305::{vg_poly1305_finalize, vg_poly1305_init, vg_poly1305_update};
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::poly1305::{vg_poly1305_finalize, vg_poly1305_init, vg_poly1305_update};

/// An incremental Poly1305 computation.
pub struct Poly1305 {
    /// The streaming state, representing the key and the message so far.
    state: [u64; 16],
    /// The message length so far, in bytes, modulo 2⁶⁴.
    count: u64,
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
        // each other or the return address.
        unsafe { vg_poly1305_init(&mut state, key) };
        Poly1305 { state, count: 0 }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, data: &[u8]) {
        let mut scratch = [0u64; 16];
        // SAFETY: `self.state` and `scratch` are valid for reads and writes of
        // 128 bytes and `data` for reads of `data.len()` bytes; they are
        // distinct objects, so they do not overlap each other or the return
        // address, and `data` does not wrap around the end of the address
        // space. `self.state` represents a message of `self.count` bytes,
        // modulo 2⁶⁴.
        unsafe {
            vg_poly1305_update(
                &mut self.state,
                self.count,
                data.as_ptr(),
                data.len(),
                &mut scratch,
            )
        };
        self.count = self.count.wrapping_add(data.len() as u64);
    }

    /// Returns the tag of everything absorbed.
    pub fn finalize(mut self) -> [u8; 16] {
        let mut tag = [0; 16];
        let mut scratch = [0u64; 16];
        // SAFETY: `self.state` and `scratch` are valid for reads and writes of
        // 128 bytes and `tag` for writes of 16 bytes; they are distinct
        // objects, so they do not overlap each other or the return address.
        // `self.state` represents a message of `self.count` bytes, modulo
        // 2⁶⁴.
        unsafe { vg_poly1305_finalize(&mut self.state, self.count, &mut tag, &mut scratch) };
        tag
    }

    /// The tag of `data` with the one-time key `key`.
    pub fn mac(key: &[u8; 32], data: &[u8]) -> [u8; 16] {
        let mut p = Self::new(key);
        p.update(data);
        p.finalize()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every message, absorbed in two pieces split at every position, and
    /// with the second piece a byte at a time, has the tag of the whole.
    #[test]
    fn incremental() {
        let key: [u8; 32] = core::array::from_fn(|i| (i * 13 + 5) as u8);
        let msg: [u8; 70] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Poly1305::mac(&key, &msg[..len]);
            for split in 0..=len {
                let mut p = Poly1305::new(&key);
                p.update(&msg[..split]);
                p.update(&msg[split..len]);
                assert_eq!(p.finalize(), expected);
                let mut p = Poly1305::new(&key);
                p.update(&msg[..split]);
                for byte in &msg[split..len] {
                    p.update(core::slice::from_ref(byte));
                }
                assert_eq!(p.finalize(), expected);
            }
        }
    }
}
