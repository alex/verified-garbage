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
//! `vg_poly1305_update` absorbs the whole blocks of the data with an
//! implementation of `vg_poly1305_blocks`, and is emitted once for each
//! (`Backend`): on x86-64, CPUs with AVX2 run `vg_poly1305_update_avx2`,
//! which absorbs them with `vg_poly1305_blocks_avx2`, four at a time once
//! there are at least 16 of them.
//!
//! A key must be used to authenticate only one message: the tags of two
//! messages under the same key reveal enough to forge others.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::poly1305::{VG_POLY1305_UPDATE_AVX2_FEATURES, vg_poly1305_update_avx2};
use crate::arch::poly1305::{vg_poly1305_finalize, vg_poly1305_init, vg_poly1305_update};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The implementations of `vg_poly1305_update`, one for each implementation
/// of `vg_poly1305_blocks`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// The baseline ISA.
    Scalar,
    /// `vg_poly1305_update_avx2`, with `vg_poly1305_blocks_avx2`.
    #[cfg(target_arch = "x86_64")]
    Avx2,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Backend {
        if f.contains(Features::of(VG_POLY1305_UPDATE_AVX2_FEATURES)) {
            Backend::Avx2
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

/// An incremental Poly1305 computation.
pub struct Poly1305 {
    /// The streaming state, representing the key and the message so far.
    state: [u64; 16],
    /// The message length so far, in bytes, modulo 2⁶⁴.
    count: u64,
    /// The implementation of `vg_poly1305_update` to call.
    backend: Backend,
}

impl Drop for Poly1305 {
    /// Wipes the state, which holds the key.
    fn drop(&mut self) {
        zeroize(&mut self.state);
    }
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
        // each other or anything on the stack (the return address and any
        // arguments), and do not wrap around the end of the address space.
        unsafe { vg_poly1305_init(&mut state, key) };
        Poly1305 {
            state,
            count: 0,
            backend: Backend::select(detected()),
        }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, data: &[u8]) {
        let mut scratch = [0u64; 16];
        let update = match self.backend {
            Backend::Scalar => vg_poly1305_update,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx2 => vg_poly1305_update_avx2,
        };
        // SAFETY: `self.state` and `scratch` are valid for reads and writes of
        // 128 bytes and `data` for reads of `data.len()` bytes; they are
        // distinct objects, so they do not overlap each other or anything on
        // the stack (the return address, any arguments, and the stack below
        // the stack pointer the calls use), and do not wrap around the end of
        // the address space. `self.state` represents a message of
        // `self.count` bytes, modulo 2⁶⁴. The CPU has the features of the
        // implementation selected (`Backend::select`).
        unsafe {
            update(
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
        // objects, so they do not overlap each other or anything on the stack
        // (the return address and any arguments), and do not wrap around the
        // end of the address space. `self.state` represents a message of
        // `self.count` bytes, modulo 2⁶⁴.
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

    /// The implementation chosen gives the same tag as the scalar one, for
    /// lengths around the number of blocks from which the vector code runs
    /// (16) and multiples of four blocks, in one piece and in two split at
    /// many positions.
    #[test]
    fn implementations_agree() {
        let key: [u8; 32] = core::array::from_fn(|i| (i * 11 + 1) as u8);
        let msg: [u8; 1100] = core::array::from_fn(|i| (i * 31 + 7) as u8);
        for len in [
            0, 1, 15, 16, 17, 63, 64, 65, 255, 256, 257, 271, 272, 273, 319, 320, 321, 1024, 1100,
        ] {
            let mut scalar = Poly1305::new(&key);
            scalar.backend = Backend::Scalar;
            scalar.update(&msg[..len]);
            let expected = scalar.finalize();
            assert_eq!(Poly1305::mac(&key, &msg[..len]), expected);
            for split in (0..=len).step_by(13) {
                let mut p = Poly1305::new(&key);
                p.update(&msg[..split]);
                p.update(&msg[split..len]);
                assert_eq!(p.finalize(), expected);
            }
        }
    }

    /// The implementation chosen for each set of features.
    #[test]
    fn select() {
        assert_eq!(Poly1305::new(&[0; 32]).backend, Backend::select(detected()));
        #[cfg(target_arch = "x86_64")]
        {
            use crate::arch::poly1305::VG_POLY1305_BLOCKS_AVX2_FEATURES;
            let avx2 = Features::of(VG_POLY1305_UPDATE_AVX2_FEATURES);
            // The instance for AVX2 needs the features of the
            // implementation of `vg_poly1305_blocks` it calls.
            assert_eq!(avx2, Features::of(VG_POLY1305_BLOCKS_AVX2_FEATURES));
            assert_eq!(Backend::select(avx2), Backend::Avx2);
            assert_eq!(Backend::select(Features::of(&["avx"])), Backend::Scalar);
        }
    }
}
