//! ChaCha20 (RFC 8439), with the 16-byte nonce of OpenSSL and
//! pyca/cryptography.
//!
//! The block function is the verified assembly primitive `vg_chacha20_block`
//! for the target architecture (contract `VG.Spec.ChaCha20.blockContract`);
//! this module builds the state
//! (RFC 8439 §2.3), XORs the keystream into the data (§2.4) and advances the
//! block counter. Whole blocks of data are XORed with the verified
//! `vg_chacha20_xor` (contract `VG.Spec.ChaCha20.xorContract`), which calls
//! the block function.
//!
//! The 16-byte nonce is the initial block counter (4 bytes, little-endian)
//! followed by the 12-byte RFC 8439 nonce, i.e. state words 12–15. As in
//! RFC 8439 (and pyca/cryptography), the block counter is word 12 alone, so
//! a keystream starting at block counter `c` is 2³² − `c` blocks long:
//! applying more of it panics, rather than wrapping the counter around or
//! carrying it into word 13, the first word of the nonce, as OpenSSL does
//! (the keystream past that point would be another nonce's, e.g. after
//! 64 bytes from `c = 0xffffffff`).
//!
//! On x86-64, CPUs with AVX-512F run `vg_chacha20_xor_avx512` instead, which
//! has the same contract and XORs sixteen blocks at a time, and other CPUs
//! with AVX2 run `vg_chacha20_xor_avx2`, which XORs eight.
//! On AArch64, the NEON backend computes four quarter rounds in parallel
//! within each block, including buffered partial blocks.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::chacha20::{
    VG_CHACHA20_XOR_AVX2_FEATURES, VG_CHACHA20_XOR_AVX512_FEATURES, vg_chacha20_xor_avx2,
    vg_chacha20_xor_avx512,
};
use crate::arch::chacha20::{vg_chacha20_block, vg_chacha20_xor};
#[cfg(target_arch = "aarch64")]
use crate::arch::chacha20::{vg_chacha20_block_neon, vg_chacha20_xor_neon};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The constants `"expand 32-byte k"` (RFC 8439 §2.3).
const CONSTANTS: [u32; 4] = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];

/// The 64 bytes of keystream for `state`.
fn block(state: &[u32; 16], backend: Backend) -> [u8; 64] {
    let mut buf = [0u32; 64];
    let f = match backend {
        Backend::Scalar => vg_chacha20_block,
        #[cfg(target_arch = "aarch64")]
        Backend::Neon => vg_chacha20_block_neon,
        #[cfg(target_arch = "x86_64")]
        Backend::Avx2 | Backend::Avx512 => vg_chacha20_block,
    };
    // SAFETY: `state` is valid for reads of 64 bytes and `buf` for reads and
    // writes of 256 bytes; they are distinct objects, so they do not overlap
    // each other or the return address.
    unsafe { f(state, &mut buf) };
    let mut out = [0u8; 64];
    for (o, word) in out.as_chunks_mut::<4>().0.iter_mut().zip(&buf[..16]) {
        *o = word.to_le_bytes();
    }
    out
}

/// The little-endian words of `bytes`.
fn words<const N: usize>(bytes: &[u8]) -> [u32; N] {
    core::array::from_fn(|i| u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()))
}

/// The implementations of `vg_chacha20_xor`, which ChaCha20-Poly1305 follows
/// (`crate::chacha20poly1305`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// Constant-time scalar code, for the target's baseline ISA.
    Scalar,
    /// Four parallel 32-bit lanes in baseline AArch64 AdvSIMD.
    #[cfg(target_arch = "aarch64")]
    Neon,
    /// AVX2, eight blocks at a time.
    #[cfg(target_arch = "x86_64")]
    Avx2,
    /// AVX-512F, sixteen blocks at a time.
    #[cfg(target_arch = "x86_64")]
    Avx512,
}

impl Backend {
    /// AdvSIMD is part of our AArch64 baseline. Tracking it also lets
    /// `VG_CPU_FEATURES=none` exercise the scalar implementation.
    #[cfg(target_arch = "aarch64")]
    pub(crate) fn select(f: Features) -> Backend {
        if f.contains(Features::of(&["neon"])) {
            Backend::Neon
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select(f: Features) -> Backend {
        Backend::select_for(
            f,
            VG_CHACHA20_XOR_AVX512_FEATURES,
            VG_CHACHA20_XOR_AVX2_FEATURES,
        )
    }

    /// The best implementation a CPU with the features `f` can run, for
    /// functions whose instances for AVX-512 and AVX2 need the features
    /// `avx512` and `avx2` (ChaCha20-Poly1305's, which also call Poly1305
    /// with AVX2, need more than `vg_chacha20_xor`'s).
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select_for(f: Features, avx512: &[&str], avx2: &[&str]) -> Backend {
        if f.contains(Features::of(avx512)) {
            Backend::Avx512
        } else if f.contains(Features::of(avx2)) {
            Backend::Avx2
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    pub(crate) fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

/// A ChaCha20 keystream, applied incrementally.
pub struct ChaCha20 {
    state: [u32; 16],
    keystream: [u8; 64],
    /// How many bytes of `keystream` have been used.
    used: usize,
    /// How many bytes of keystream are left before the block counter would
    /// wrap around: those left in `keystream` and in the blocks from the
    /// counter in word 12 to the last one, `0xffffffff`.
    remaining: u64,
    backend: Backend,
}

impl Drop for ChaCha20 {
    /// Wipes the state, which holds the key, and the buffered keystream.
    fn drop(&mut self) {
        zeroize(&mut self.state);
        zeroize(&mut self.keystream);
    }
}

impl ChaCha20 {
    /// The size of a key, in bytes.
    pub const KEY_SIZE: usize = 32;
    /// The size of a nonce (initial block counter and RFC 8439 nonce), in bytes.
    pub const NONCE_SIZE: usize = 16;

    /// Starts the keystream for `key` and `nonce` (the initial block counter,
    /// little-endian, followed by the 12-byte RFC 8439 nonce).
    pub fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        let mut state = [0u32; 16];
        state[..4].copy_from_slice(&CONSTANTS);
        state[4..12].copy_from_slice(&words::<8>(key));
        let mut c = ChaCha20 {
            state,
            keystream: [0; 64],
            used: 64,
            remaining: 0,
            backend: Backend::select(detected()),
        };
        c.reset_nonce(nonce);
        c
    }

    /// Restarts the keystream, with the same key, for `nonce`.
    pub fn reset_nonce(&mut self, nonce: &[u8; 16]) {
        self.state[12..].copy_from_slice(&words::<4>(nonce));
        self.used = 64;
        self.remaining = 64 * ((1 << 32) - u64::from(self.state[12]));
    }

    /// XORs the next `data.len()` bytes of the keystream into `data`
    /// (encrypting or decrypting it).
    ///
    /// # Panics
    ///
    /// If the keystream is not that long: if the block counter would pass
    /// `0xffffffff`, i.e. if more than 64 × (2³² − `c`) bytes in all would
    /// have been applied since the nonce (with initial block counter `c`) was
    /// set. `data` is then left unchanged.
    pub fn apply_keystream(&mut self, data: &mut [u8]) {
        self.remaining = self
            .remaining
            .checked_sub(data.len() as u64)
            .expect("ChaCha20 block counter would overflow");
        let (head, rest) = data.split_at_mut((64 - self.used).min(data.len()));
        self.xor_bytes(head);
        let rest = self.xor_blocks(rest);
        self.xor_bytes(rest);
    }

    /// Advances the block counter in word 12 by `n`. `remaining` keeps it
    /// from passing `0xffffffff` (it wraps around to 0 only after the last
    /// block, and is not used again).
    fn advance(&mut self, n: u64) {
        self.state[12] = self.state[12].wrapping_add(n as u32);
    }

    /// XORs the keystream into `data` a byte at a time, from the buffered
    /// block and then from new ones.
    fn xor_bytes(&mut self, data: &mut [u8]) {
        for byte in data {
            if self.used == 64 {
                self.keystream = block(&self.state, self.backend);
                self.used = 0;
                self.advance(1);
            }
            *byte ^= self.keystream[self.used];
            self.used += 1;
        }
    }

    /// XORs the keystream into the whole blocks at the start of `data`, from
    /// the current counter (no block may be buffered), and returns the rest.
    fn xor_blocks<'a>(&mut self, data: &'a mut [u8]) -> &'a mut [u8] {
        let (blocks, rest) = data.split_at_mut(data.len() / 64 * 64);
        if !blocks.is_empty() {
            // `remaining` (checked by `apply_keystream`) keeps the blocks
            // within those left before word 12 wraps around.
            let mut state = self.state;
            let mut buf = [0u32; 80];
            let f = match self.backend {
                Backend::Scalar => vg_chacha20_xor,
                #[cfg(target_arch = "aarch64")]
                Backend::Neon => vg_chacha20_xor_neon,
                #[cfg(target_arch = "x86_64")]
                Backend::Avx2 => vg_chacha20_xor_avx2,
                #[cfg(target_arch = "x86_64")]
                Backend::Avx512 => vg_chacha20_xor_avx512,
            };
            // SAFETY: `state` is valid for reads and writes of 64 bytes,
            // `blocks` for reads and writes of `blocks.len()` bytes and `buf` for
            // reads and writes of 320 bytes; they are distinct objects, so
            // they do not overlap each other, the stack frame of the call
            // (the return address and any arguments on the stack) or the
            // stack below it, and do not wrap around the end of the address
            // space. The CPU has the features of the implementation selected.
            unsafe { f(&mut state, blocks.as_mut_ptr(), blocks.len(), &mut buf) };
            self.advance((blocks.len() / 64) as u64);
        }
        rest
    }
}

#[cfg(test)]
mod tests {
    use super::{Backend, ChaCha20};
    use crate::cpu::detected;

    fn unhex<const N: usize>(s: &str) -> [u8; N] {
        let mut out = [0u8; N];
        for (i, o) in out.iter_mut().enumerate() {
            *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }

    /// A fixed key, `00:01:…:1f`.
    fn key() -> [u8; 32] {
        core::array::from_fn(|i| i as u8)
    }

    /// A 16-byte nonce from an RFC 8439 block counter and nonce.
    fn nonce(counter: u32, nonce: &[u8; 12]) -> [u8; 16] {
        let mut n = [0u8; 16];
        n[..4].copy_from_slice(&counter.to_le_bytes());
        n[4..].copy_from_slice(nonce);
        n
    }

    /// The first `N` bytes of keystream.
    fn keystream<const N: usize>(key: &[u8; 32], nonce: &[u8; 16]) -> [u8; N] {
        let mut out = [0u8; N];
        ChaCha20::new(key, nonce).apply_keystream(&mut out);
        out
    }

    /// Applying the keystream in two pieces, or a byte at a time, is the
    /// same as applying it at once, for every split around block boundaries.
    #[test]
    fn incremental() {
        let n = nonce(7, &[3; 12]);
        let expected = keystream::<200>(&key(), &n);
        for split in 0..=200 {
            let mut data = [0u8; 200];
            let mut c = ChaCha20::new(&key(), &n);
            c.apply_keystream(&mut data[..split]);
            c.apply_keystream(&mut data[split..]);
            assert_eq!(data, expected);
        }
        let mut data = [0u8; 200];
        let mut c = ChaCha20::new(&key(), &n);
        for byte in data.chunks_mut(1) {
            c.apply_keystream(byte);
        }
        assert_eq!(data, expected);
    }

    /// `reset_nonce` restarts the keystream.
    #[test]
    fn reset_nonce() {
        let (n1, n2) = (nonce(0, &[1; 12]), nonce(5, &[2; 12]));
        let mut c = ChaCha20::new(&key(), &n1);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        c.reset_nonce(&n2);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        assert_eq!(data, keystream::<100>(&key(), &n2));
    }

    /// The keystream from block counter 0xffffffff is one block long,
    /// however it is applied, and `reset_nonce` starts a new one.
    #[test]
    fn last_block() {
        let n = nonce(0xffff_ffff, &unhex("0900000011223344aabbccdd"));
        let ks = keystream::<64>(&key(), &n);
        let mut c = ChaCha20::new(&key(), &n);
        let mut data = [0u8; 64];
        c.apply_keystream(&mut data[..10]);
        c.apply_keystream(&mut data[10..]);
        c.apply_keystream(&mut []);
        assert_eq!(data, ks);
        c.reset_nonce(&n);
        let mut data = [0u8; 64];
        c.apply_keystream(&mut data);
        assert_eq!(data, ks);
    }

    /// Applies `first` bytes of the keystream from block counter `counter`
    /// and then `then` more, which the tests below make too many.
    fn overflow(counter: u32, first: usize, then: usize) {
        let mut c = ChaCha20::new(&key(), &nonce(counter, &[4; 12]));
        let mut data = [0u8; 192];
        c.apply_keystream(&mut data[..first]);
        c.apply_keystream(&mut data[..then]);
    }

    /// Applying keystream past block counter 0xffffffff panics: in whole
    /// blocks, byte by byte, and after part of the last block.
    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_whole_blocks() {
        overflow(0xffff_fffe, 0, 64 * 3);
    }

    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_after_blocks() {
        overflow(0xffff_fffe, 64, 64 * 2);
    }

    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_one_byte() {
        overflow(0xffff_ffff, 64, 1);
    }

    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_partial_block() {
        overflow(0xffff_ffff, 10, 55);
    }

    /// The implementation chosen gives the same keystream as the scalar one,
    /// for lengths around multiples of eight and sixteen blocks, in one call
    /// and split,
    /// and up to the last block counter.
    #[test]
    fn implementations_agree() {
        const LEN: usize = 16 * 64 * 2 + 64 * 3;
        for counter in [0, 0u32.wrapping_sub((LEN / 64) as u32)] {
            let n = nonce(counter, &[5; 12]);
            let mut expected = [0u8; LEN];
            let mut scalar = ChaCha20::new(&key(), &n);
            scalar.backend = Backend::Scalar;
            scalar.apply_keystream(&mut expected);
            let mut once = [0u8; LEN];
            ChaCha20::new(&key(), &n).apply_keystream(&mut once);
            assert_eq!(once, expected);
            for split in (0..=LEN).step_by(61) {
                let mut data = [0u8; LEN];
                let mut c = ChaCha20::new(&key(), &n);
                c.apply_keystream(&mut data[..split]);
                c.apply_keystream(&mut data[split..]);
                assert_eq!(data, expected);
            }
        }
    }

    /// The implementation chosen for each set of features.
    #[test]
    fn select() {
        let best = ChaCha20::new(&key(), &nonce(0, &[0; 12])).backend;
        assert_eq!(best, Backend::select(detected()));
        #[cfg(target_arch = "aarch64")]
        {
            use crate::cpu::Features;
            assert_eq!(Backend::select(Features::of(&["neon"])), Backend::Neon);
            assert_eq!(Backend::select(Features::of(&[])), Backend::Scalar);
        }
        #[cfg(target_arch = "x86_64")]
        {
            use crate::arch::chacha20::{
                VG_CHACHA20_XOR_AVX2_FEATURES, VG_CHACHA20_XOR_AVX512_FEATURES,
            };
            use crate::cpu::Features;
            let avx2 = Features::of(VG_CHACHA20_XOR_AVX2_FEATURES);
            let avx512 = Features::of(VG_CHACHA20_XOR_AVX512_FEATURES);
            assert_eq!(Backend::select(avx2), Backend::Avx2);
            assert_eq!(Backend::select(avx512), Backend::Avx512);
            assert_eq!(
                Backend::select(Features::all(&[
                    VG_CHACHA20_XOR_AVX2_FEATURES,
                    VG_CHACHA20_XOR_AVX512_FEATURES
                ])),
                Backend::Avx512
            );
            assert_eq!(Backend::select(Features::of(&["avx"])), Backend::Scalar);
        }
    }
}
