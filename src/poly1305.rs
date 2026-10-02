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
//! (`Backend`): on x86-64, CPUs with AVX-512F and AVX2 run
//! `vg_poly1305_update_avx512`, which absorbs them with
//! `vg_poly1305_blocks_avx512`, eight at a time once there are at least 40 of
//! them (and fewer with `vg_poly1305_blocks_avx2`), and other CPUs with AVX2
//! `vg_poly1305_update_avx2`, which absorbs them with
//! `vg_poly1305_blocks_avx2`, four at a time once there are at least 32 of
//! them.
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
use crate::arch::poly1305::{
    VG_POLY1305_UPDATE_AVX2_FEATURES, VG_POLY1305_UPDATE_AVX512_FEATURES, vg_poly1305_update_avx2,
    vg_poly1305_update_avx512,
};
use crate::arch::poly1305::{vg_poly1305_finalize, vg_poly1305_init, vg_poly1305_update};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

pub use crate::hmac::InvalidMac;

/// The implementations of `vg_poly1305_update`, one for each implementation
/// of `vg_poly1305_blocks`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// The baseline ISA.
    Scalar,
    /// `vg_poly1305_update_avx2`, with `vg_poly1305_blocks_avx2`.
    #[cfg(target_arch = "x86_64")]
    Avx2,
    /// `vg_poly1305_update_avx512`, with `vg_poly1305_blocks_avx512`.
    #[cfg(target_arch = "x86_64")]
    Avx512,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Backend {
        if f.contains(Features::of(VG_POLY1305_UPDATE_AVX512_FEATURES)) {
            Backend::Avx512
        } else if f.contains(Features::of(VG_POLY1305_UPDATE_AVX2_FEATURES)) {
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
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512 => vg_poly1305_update_avx512,
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

    /// Checks that `tag` is the tag of everything absorbed, in constant
    /// time: the time taken does not depend on where, or whether, `tag`
    /// differs from it (its length is public). `tag` must be the whole tag,
    /// of [`Self::TAG_SIZE`] bytes; a truncated one is rejected.
    pub fn verify(self, tag: &[u8]) -> Result<(), InvalidMac> {
        if crate::ct::eq(&self.finalize(), tag) {
            Ok(())
        } else {
            Err(InvalidMac)
        }
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

    /// `verify` accepts the tag and rejects any other: one with a bit
    /// flipped in its first, a middle or its last byte, a truncated tag and
    /// a longer one.
    #[test]
    fn verify() {
        let key: [u8; 32] = core::array::from_fn(|i| (i * 13 + 5) as u8);
        let data = b"Cryptographic Forum Research Group";
        let tag = Poly1305::mac(&key, data);
        let check = |t: &[u8]| {
            let mut p = Poly1305::new(&key);
            p.update(data);
            p.verify(t)
        };
        assert_eq!(check(&tag), Ok(()));
        for i in [0, 7, 15] {
            let mut bad = tag;
            bad[i] ^= 1;
            assert_eq!(check(&bad), Err(InvalidMac));
        }
        assert_eq!(check(&tag[..15]), Err(InvalidMac));
        assert_eq!(check(&[]), Err(InvalidMac));
        let mut longer = [0u8; 17];
        longer[..16].copy_from_slice(&tag);
        assert_eq!(check(&longer), Err(InvalidMac));
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
            0, 1, 15, 16, 17, 63, 64, 65, 255, 256, 257, 271, 272, 273, 319, 320, 321, 495, 496,
            511, 512, 513, 527, 528, 529, 623, 624, 625, 639, 640, 641, 1024, 1100,
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
            use crate::arch::poly1305::{
                VG_POLY1305_BLOCKS_AVX2_FEATURES, VG_POLY1305_BLOCKS_AVX512_FEATURES,
            };
            let avx2 = Features::of(VG_POLY1305_UPDATE_AVX2_FEATURES);
            let avx512 = Features::of(VG_POLY1305_UPDATE_AVX512_FEATURES);
            // The instances need the features of the implementations of
            // `vg_poly1305_blocks` they call.
            assert_eq!(avx2, Features::of(VG_POLY1305_BLOCKS_AVX2_FEATURES));
            assert_eq!(avx512, Features::of(VG_POLY1305_BLOCKS_AVX512_FEATURES));
            assert_eq!(Backend::select(avx512), Backend::Avx512);
            assert_eq!(Backend::select(avx2), Backend::Avx2);
            // AVX-512F alone is not enough: the AVX-512 instance calls the
            // AVX2 one.
            assert_eq!(
                Backend::select(Features::of(&["avx", "avx512f"])),
                Backend::Scalar
            );
            assert_eq!(Backend::select(Features::of(&["avx"])), Backend::Scalar);
        }
    }
}
