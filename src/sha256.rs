//! SHA-256 (FIPS 180-4).
//!
//! The compression function is the verified assembly primitive
//! `vg_sha256_compress` for the target architecture (contracts
//! `VG.Spec.Sha256.compressX86_64`, `compressAArch64` and `compressArm`); this
//! module adds the buffering, padding (§5.1.1) and output encoding around it.

#[cfg(target_arch = "aarch64")]
use crate::asm::aarch64::sha256::vg_sha256_compress;
#[cfg(target_arch = "arm")]
use crate::asm::arm::sha256::vg_sha256_compress;
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::sha256::vg_sha256_compress;

/// The initial hash value `H⁽⁰⁾` (FIPS 180-4 §5.3.3).
const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Updates `state` with every 64-byte block of `blocks` (whose length must be
/// a multiple of 64).
fn compress(state: &mut [u32; 8], blocks: &[u8]) {
    debug_assert_eq!(blocks.len() % Sha256::BLOCK_SIZE, 0);
    let mut scratch = [0u64; 14];
    // SAFETY: `state` is valid for reads and writes of 32 bytes, `blocks` for
    // reads of `64 * (blocks.len() / 64)` bytes and `scratch` for reads and
    // writes of 112 bytes; they are distinct objects, so they do not overlap
    // each other or the return address.
    unsafe {
        vg_sha256_compress(
            state,
            blocks.as_ptr(),
            blocks.len() / Sha256::BLOCK_SIZE,
            &mut scratch,
        )
    }
}

/// An incremental SHA-256 computation.
///
/// Messages are limited to 2⁶¹ − 1 bytes (2⁶⁴ − 1 bits), as in FIPS 180-4.
#[derive(Clone)]
pub struct Sha256 {
    state: [u32; 8],
    buffer: [u8; 64],
    buffered: usize,
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
        Sha256 {
            state: H0,
            buffer: [0; 64],
            buffered: 0,
            length: 0,
        }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, mut data: &[u8]) {
        self.length = self.length.wrapping_add(data.len() as u64);
        if self.buffered > 0 {
            let take = (Self::BLOCK_SIZE - self.buffered).min(data.len());
            self.buffer[self.buffered..self.buffered + take].copy_from_slice(&data[..take]);
            self.buffered += take;
            data = &data[take..];
            if self.buffered < Self::BLOCK_SIZE {
                return;
            }
            compress(&mut self.state, &self.buffer);
            self.buffered = 0;
        }
        let whole = data.len() - data.len() % Self::BLOCK_SIZE;
        compress(&mut self.state, &data[..whole]);
        let rest = &data[whole..];
        self.buffer[..rest.len()].copy_from_slice(rest);
        self.buffered = rest.len();
    }

    /// Pads the message (FIPS 180-4 §5.1.1) and returns its digest.
    pub fn finalize(mut self) -> [u8; 32] {
        let bits = self.length.wrapping_mul(8);
        // `0x80`, then zeros up to 56 bytes modulo 64, then the length.
        let zeros = (119 - self.buffered) % Self::BLOCK_SIZE;
        let mut padding = [0u8; 72];
        padding[0] = 0x80;
        padding[1 + zeros..9 + zeros].copy_from_slice(&bits.to_be_bytes());
        self.update(&padding[..9 + zeros]);
        debug_assert_eq!(self.buffered, 0);
        let mut digest = [0u8; 32];
        for (out, word) in digest.as_chunks_mut::<4>().0.iter_mut().zip(self.state) {
            *out = word.to_be_bytes();
        }
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
