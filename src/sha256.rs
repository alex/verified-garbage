//! SHA-256 (FIPS 180-4).
//!
//! The whole computation is verified assembly: `vg_sha256_init`,
//! `vg_sha256_update` and `vg_sha256_finalize` (contracts
//! `VG.Spec.Sha256.initX86_64`, `updateX86_64` and `finalizeX86_64`) maintain
//! a streaming state that represents the message absorbed so far
//! (`VG.Spec.Sha256.Repr`: the hash value of its whole blocks, and its
//! remaining bytes), and pad it and output the digest. This module only keeps
//! that state together with the message length, which the contracts take as
//! an argument.
//!
//! That is the case on x86-64. On AArch64 and 32-bit ARM, whose streaming
//! functions are not verified yet, only the compression function is verified
//! assembly (see the `compress` module).

#[cfg(any(target_arch = "aarch64", target_arch = "arm"))]
mod compress;
#[cfg(any(target_arch = "aarch64", target_arch = "arm"))]
pub use compress::Sha256;

#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::sha256::{vg_sha256_finalize, vg_sha256_init, vg_sha256_update};

#[cfg(target_arch = "x86_64")]
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

#[cfg(target_arch = "x86_64")]
impl Default for Sha256 {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(target_arch = "x86_64")]
impl Sha256 {
    /// The size of a digest, in bytes.
    pub const OUTPUT_SIZE: usize = 32;
    /// The size of a message block, in bytes.
    pub const BLOCK_SIZE: usize = 64;

    /// Starts a new computation.
    pub fn new() -> Self {
        let mut state = [0; 96];
        // SAFETY: `state` is valid for writes of 96 bytes, and is a distinct
        // object from the return address.
        unsafe { vg_sha256_init(&mut state) };
        Sha256 { state, length: 0 }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, data: &[u8]) {
        let mut scratch = [0u64; 20];
        // SAFETY: `self.state` is valid for reads and writes of 96 bytes,
        // `data` for reads of `data.len()` bytes and `scratch` for reads and
        // writes of 160 bytes; they are distinct objects, so they do not
        // overlap each other or the return address. `self.length` is the
        // length of the message `self.state` represents, modulo 2⁶⁴.
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
        // other or the return address. `self.length` is the length of the
        // message `self.state` represents, modulo 2⁶⁴.
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
