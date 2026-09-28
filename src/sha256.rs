//! SHA-256 (FIPS 180-4).
//!
//! The whole computation is verified assembly: `vg_sha256_init`,
//! `vg_sha256_update` and `vg_sha256_finalize` for the target architecture
//! (contracts `VG.Spec.Sha256.initContract`, `updateContract` and
//! `finalizeContract`) maintain a streaming state
//! that represents the message absorbed so far (`VG.Spec.Sha256.Repr`: the
//! hash value of its whole blocks, and its remaining bytes), and pad it and
//! output the digest. This module only keeps that state together with the
//! message length, which the contracts take as an argument.

#[cfg(target_arch = "aarch64")]
use crate::asm::aarch64::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};
#[cfg(target_arch = "arm")]
use crate::asm::arm::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};
#[cfg(target_arch = "x86")]
use crate::asm::x86::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};

/// An incremental SHA-256 computation.
///
/// Messages are limited to 2⁶¹ − 1 bytes (2⁶⁴ − 1 bits), as in FIPS 180-4.
#[derive(Clone)]
pub struct Sha256 {
    /// The streaming state, representing the message so far.
    state: [u8; 96],
    /// The message length so far, in bytes (modulo 2⁶⁴).
    length: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Self::new()
    }
}

impl Sha256 {
    /// The size of a digest, in bytes.
    pub const OUTPUT_SIZE: usize = 32;
    /// The size of a message block, in bytes.
    pub const BLOCK_SIZE: usize = 64;

    /// Starts a new computation.
    pub fn new() -> Self {
        let mut state = [0; 96];
        // SAFETY: `state` is valid for writes of 96 bytes, and is a distinct
        // object from the return address (on x86-64 and x86) and the argument
        // on the stack (on x86); as a Rust object, it does not wrap around the
        // end of the address space.
        unsafe { vg_sha256_init(&mut state) };
        Sha256 { state, length: 0 }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, data: &[u8]) {
        let mut scratch = [0u64; 20];
        // SAFETY: `self.state` is valid for reads and writes of 96 bytes,
        // `data` for reads of `data.len()` bytes and `scratch` for reads and
        // writes of 160 bytes; they are distinct objects, so they do not
        // overlap each other, the return address (on x86-64 and x86) or the
        // arguments on the stack (on 32-bit ARM and x86), and do not wrap
        // around the end of the address space. `self.length` is the length of
        // the message `self.state` represents, modulo 2⁶⁴.
        unsafe {
            vg_sha256_update(
                &mut self.state,
                self.length,
                data.as_ptr(),
                data.len(),
                &mut scratch,
            )
        };
        self.length = self.length.wrapping_add(data.len() as u64);
    }

    /// Pads the message (FIPS 180-4 §5.1.1) and returns its digest.
    pub fn finalize(mut self) -> [u8; 32] {
        let mut digest = [0; 32];
        let mut scratch = [0u64; 20];
        // SAFETY: `self.state` is valid for reads and writes of 96 bytes,
        // `digest` for writes of 32 bytes and `scratch` for reads and writes
        // of 160 bytes; they are distinct objects, so they do not overlap each
        // other, the return address (on x86-64 and x86) or the arguments on
        // the stack (on 32-bit ARM and x86), and do not wrap around the end of
        // the address space. `self.length` is the length of the message
        // `self.state` represents, modulo 2⁶⁴.
        unsafe { vg_sha256_finalize(&mut self.state, self.length, &mut digest, &mut scratch) };
        digest
    }

    /// The digest of `data`.
    pub fn digest(data: &[u8]) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(data);
        h.finalize()
    }
}

impl crate::hash::HashFunction for Sha256 {
    const OUTPUT_SIZE: usize = Sha256::OUTPUT_SIZE;
    const BLOCK_SIZE: usize = Sha256::BLOCK_SIZE;
    type Output = [u8; 32];

    fn new() -> Self {
        Sha256::new()
    }

    fn update(&mut self, data: &[u8]) {
        Sha256::update(self, data)
    }

    fn finalize(self) -> [u8; 32] {
        Sha256::finalize(self)
    }
}

#[cfg(test)]
mod tests {
    use super::Sha256;

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha256::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha256::default();
                h.update(&msg[..split]);
                let copy = h.clone();
                h.update(&msg[split..len]);
                assert_eq!(h.finalize(), expected);
                let mut h = copy;
                for byte in &msg[split..len] {
                    h.update(core::slice::from_ref(byte));
                }
                assert_eq!(h.finalize(), expected);
            }
        }
    }
}
