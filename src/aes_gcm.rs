//! AES-GCM (NIST SP 800-38D) with 128-, 192- and 256-bit AES keys.
//!
//! The block cipher and GHASH are the verified assembly primitives for the
//! target architecture: `vg_aes_expand_key` (contract
//! `VG.Spec.Aes.expandKeyContract`), `vg_aes_ctr32` (counter mode with
//! `inc32` over whole blocks, `VG.Spec.Gcm.ctr32Contract`) and `vg_ghash`
//! (GHASH over whole blocks, `VG.Spec.Gcm.ghashContract`). This module does
//! the rest of GCM-AE and GCM-AD (§7): the pre-counter block `J0`, the final
//! partial block, the zero padding and length block that GHASH absorbs, the
//! tag, and the length limits of §5.2.1.1. Decryption checks the tag, in
//! constant time, before it decrypts anything.
//!
//! On x86-64, CPUs with AES-NI, PCLMULQDQ and SSSE3 run
//! `vg_aes_expand_key_aesni`, `vg_aes_ctr32_aesni` and `vg_ghash_pclmul`
//! instead, which have the same contracts; on AArch64, CPUs with the AES and
//! PMULL extensions run `vg_aes_expand_key_aes`, `vg_aes_ctr32_aes` and
//! `vg_ghash_pmull`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::aes::{
    VG_AES_CTR32_AES_FEATURES, VG_AES_EXPAND_KEY_AES_FEATURES, vg_aes_ctr32_aes,
    vg_aes_expand_key_aes,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes::{
    VG_AES_CTR32_AESNI_FEATURES, VG_AES_EXPAND_KEY_AESNI_FEATURES, vg_aes_ctr32_aesni,
    vg_aes_expand_key_aesni,
};
use crate::arch::aes::{vg_aes_ctr32, vg_aes_expand_key};
use crate::arch::gcm::vg_ghash;
#[cfg(target_arch = "x86_64")]
use crate::arch::gcm::{VG_GHASH_PCLMUL_FEATURES, vg_ghash_pclmul};
#[cfg(target_arch = "aarch64")]
use crate::arch::gcm::{VG_GHASH_PMULL_FEATURES, vg_ghash_pmull};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// A 16-byte block.
type Block = [u8; 16];

/// The largest plaintext (and ciphertext), in bytes: `2^39 − 256` bits
/// (SP 800-38D §5.2.1.1).
const MAX_TEXT: u64 = (1 << 36) - 32;

/// The largest additional data, in bytes: `2^64 − 1` bits, rounded down to
/// whole bytes (SP 800-38D §5.2.1.1).
const MAX_AAD: u64 = (1 << 61) - 1;

/// The tag lengths SP 800-38D §5.2.1.2 allows, in bytes.
const TAG_LENGTHS: [usize; 7] = [4, 8, 12, 13, 14, 15, 16];

/// Why an AES-GCM operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The key is not 16, 24 or 32 bytes long.
    InvalidKeyLength,
    /// The nonce is empty.
    InvalidNonceLength,
    /// The plaintext or ciphertext is longer than `2^36 − 32` bytes.
    InvalidTextLength,
    /// The additional data is longer than `2^61 − 1` bytes.
    InvalidAadLength,
    /// The tag is not 4, 8, 12, 13, 14, 15 or 16 bytes long.
    InvalidTagLength,
    /// The tag does not match: the ciphertext, the additional data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
    /// [`AesGcmStream::update_aad`] was called after
    /// [`AesGcmStream::update`]: GCM authenticates all of the additional
    /// data before the text.
    AadAfterText,
    /// [`AesGcmStream::set_tag`] was called when encrypting.
    TagWhenEncrypting,
    /// [`AesGcmStream::finalize`] was called when decrypting, without a tag
    /// from [`AesGcmStream::set_tag`] to check.
    MissingTag,
}

/// `len + n`, if it is at most `max`.
fn add_len(len: u64, n: usize, max: u64) -> Result<u64, ()> {
    match len.checked_add(n as u64) {
        Some(total) if total <= max => Ok(total),
        _ => Err(()),
    }
}

/// Whether `tag` is an allowed truncation of `expected`. The comparison
/// takes the same time wherever the tags differ.
fn verify(expected: &Block, tag: &[u8]) -> Result<(), Error> {
    if !TAG_LENGTHS.contains(&tag.len()) {
        return Err(Error::InvalidTagLength);
    }
    if !crate::ct::eq(&expected[..tag.len()], tag) {
        return Err(Error::TagMismatch);
    }
    Ok(())
}

/// The length block `[len(A)]_64 || [len(C)]_64` (in bits) that GHASH
/// absorbs last (§7.1 step 5).
fn lengths(aad_len: u64, text_len: u64) -> Block {
    let mut len = [0u8; 16];
    len[..8].copy_from_slice(&(aad_len * 8).to_be_bytes());
    len[8..].copy_from_slice(&(text_len * 8).to_be_bytes());
    len
}

/// An AES-GCM key: the AES key schedule and the hash subkey `H`. Its
/// [`encrypt`](Self::encrypt) and [`decrypt`](Self::decrypt) are the
/// one-shot AEAD; [`AesGcmStream`] encrypts or decrypts incrementally.
#[derive(Clone)]
pub struct AesGcm {
    schedule: [u8; 240],
    rounds: usize,
    h: Block,
    backend: Backend,
}

impl Drop for AesGcm {
    /// Wipes the key schedule and the hash subkey.
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
        zeroize(&mut self.h);
    }
}

/// The implementations of the primitives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// Constant-time scalar code, for the target's baseline ISA.
    Scalar,
    /// AES-NI and PCLMULQDQ.
    #[cfg(target_arch = "x86_64")]
    AesNi,
    /// The AES and PMULL extensions.
    #[cfg(target_arch = "aarch64")]
    ArmCrypto,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Backend {
        if f.contains(Features::all(&[
            VG_AES_EXPAND_KEY_AESNI_FEATURES,
            VG_AES_CTR32_AESNI_FEATURES,
            VG_GHASH_PCLMUL_FEATURES,
        ])) {
            Backend::AesNi
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "aarch64")]
    fn select(f: Features) -> Backend {
        if f.contains(Features::all(&[
            VG_AES_EXPAND_KEY_AES_FEATURES,
            VG_AES_CTR32_AES_FEATURES,
            VG_GHASH_PMULL_FEATURES,
        ])) {
            Backend::ArmCrypto
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

impl AesGcm {
    /// The size of a full tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Prepares `key`, which must be 16, 24 or 32 bytes long (AES-128,
    /// AES-192 or AES-256).
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
        }
        let mut k = AesGcm {
            schedule: [0; 240],
            rounds: key.len() / 4 + 6,
            h: [0; 16],
            backend: Backend::select(detected()),
        };
        let mut scratch = MaybeUninit::<[u64; 64]>::uninit();
        let (key_ptr, schedule) = (key.as_ptr(), &mut k.schedule);
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `k.schedule` and `scratch` are valid for reads and writes
        // of 240 and 512 bytes. They are distinct objects, so no two overlap,
        // nor do they overlap the return address. The CPU has the features
        // of the implementation selected. `scratch` is uninitialized: it is
        // only working space, and the contract's result does not depend on
        // what it holds.
        unsafe {
            match k.backend {
                Backend::Scalar => {
                    vg_aes_expand_key(key_ptr, key.len(), schedule, scratch.as_mut_ptr())
                }
                #[cfg(target_arch = "x86_64")]
                Backend::AesNi => {
                    vg_aes_expand_key_aesni(key_ptr, key.len(), schedule, scratch.as_mut_ptr())
                }
                #[cfg(target_arch = "aarch64")]
                Backend::ArmCrypto => {
                    vg_aes_expand_key_aes(key_ptr, key.len(), schedule, scratch.as_mut_ptr())
                }
            }
        };
        // H = CIPH_K(0^128): the keystream of a zero block.
        let mut h = [[0u8; 16]];
        k.ctr32(&mut [0; 16], &mut h);
        k.h = h[0];
        Ok(k)
    }

    /// XORs the counter-mode keystream from `counter` into `blocks`, and
    /// advances `counter` past them.
    fn ctr32(&self, counter: &mut Block, blocks: &mut [Block]) {
        let mut scratch = MaybeUninit::<[u64; 256]>::uninit();
        let f = match self.backend {
            Backend::Scalar => vg_aes_ctr32,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => vg_aes_ctr32_aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::ArmCrypto => vg_aes_ctr32_aes,
        };
        // SAFETY: `self.schedule` holds the key schedule for `self.rounds`
        // (10, 12 or 14) rounds, written by key expansion (every
        // implementation writes the same one); it is valid for reads of 240
        // bytes, `counter` for reads and writes of 16, `blocks` of
        // `16 * blocks.len()` and `scratch` (uninitialized working space,
        // as in `new`) of 2048. `counter` and `blocks` are mutable borrows and
        // `scratch` a local, so none overlaps another argument or the return
        // address. The CPU has the features of the implementation selected.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                counter,
                blocks.as_mut_ptr(),
                blocks.len(),
                scratch.as_mut_ptr(),
            )
        };
    }

    /// Continues GHASH from `y` over `data`, padded with zeros to a whole
    /// number of blocks.
    fn ghash(&self, y: &mut Block, data: &[u8]) {
        let (blocks, rest) = data.as_chunks::<16>();
        let mut scratch = MaybeUninit::<[u64; 32]>::uninit();
        let f = match self.backend {
            Backend::Scalar => vg_ghash,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => vg_ghash_pclmul,
            #[cfg(target_arch = "aarch64")]
            Backend::ArmCrypto => vg_ghash_pmull,
        };
        // SAFETY: `self.h` is valid for reads of 16 bytes, `y` for reads and
        // writes of 16, `blocks` for reads of `16 * blocks.len()` and
        // `scratch` (uninitialized working space, as in `new`) for reads and
        // writes of 256. `y` is a mutable borrow and `scratch` a local, so
        // they overlap nothing else. The CPU has the features of the
        // implementation selected.
        unsafe {
            f(
                &self.h,
                y,
                blocks.as_ptr(),
                blocks.len(),
                scratch.as_mut_ptr(),
            )
        };
        if !rest.is_empty() {
            let mut last = [[0u8; 16]];
            last[0][..rest.len()].copy_from_slice(rest);
            // SAFETY: as above.
            unsafe { f(&self.h, y, last.as_ptr(), 1, scratch.as_mut_ptr()) };
        }
    }

    /// The pre-counter block `J0` for `nonce` (§7.1 step 2), after checking
    /// that the nonce is not empty (§5.2.1.1).
    fn j0(&self, nonce: &[u8]) -> Result<Block, Error> {
        let mut j0 = [0u8; 16];
        match nonce.len() {
            0 => return Err(Error::InvalidNonceLength),
            12 => {
                j0[..12].copy_from_slice(nonce);
                j0[15] = 1;
            }
            n => {
                self.ghash(&mut j0, nonce);
                self.ghash(&mut j0, &lengths(0, n as u64));
            }
        }
        Ok(j0)
    }

    /// `S` (§7.1 steps 4–5, from the GHASH `y` of everything but the length
    /// block) XORed with `CIPH_K(J0)`: the full tag (§7.1 step 6).
    fn tag(&self, j0: &Block, mut y: Block, aad_len: u64, text_len: u64) -> Block {
        self.ghash(&mut y, &lengths(aad_len, text_len));
        let mut t = [y];
        self.ctr32(&mut j0.clone(), &mut t);
        t[0]
    }

    /// The tag of `aad` and `ciphertext`, after checking their lengths
    /// (§5.2.1.1).
    fn tag_of(&self, j0: &Block, aad: &[u8], ciphertext: &[u8]) -> Result<Block, Error> {
        let aad_len = add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let text_len =
            add_len(0, ciphertext.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        let mut y = [0u8; 16];
        self.ghash(&mut y, aad);
        self.ghash(&mut y, ciphertext);
        Ok(self.tag(j0, y, aad_len, text_len))
    }

    /// GCTR from `inc32(J0)` (§7.1 step 3) over `data`, in place.
    fn gctr(&self, j0: &Block, data: &mut [u8]) {
        let mut counter = *j0;
        let c = u32::from_be_bytes(counter[12..].try_into().unwrap()).wrapping_add(1);
        counter[12..].copy_from_slice(&c.to_be_bytes());
        let (blocks, rest) = data.as_chunks_mut::<16>();
        self.ctr32(&mut counter, blocks);
        if !rest.is_empty() {
            let mut last = [[0u8; 16]];
            last[0][..rest.len()].copy_from_slice(rest);
            self.ctr32(&mut counter, &mut last);
            rest.copy_from_slice(&last[0][..rest.len()]);
        }
    }

    /// GCM-AE (§7.1): encrypts `buffer` in place under `nonce`, and returns
    /// the 16-byte tag authenticating the ciphertext and `aad`. A caller that
    /// wants a shorter tag truncates it (keeping its first bytes).
    ///
    /// The nonce may have any nonzero length; 12 bytes is the recommended
    /// (and fastest) one. A nonce must never be used twice with the same key.
    pub fn encrypt(&self, nonce: &[u8], aad: &[u8], buffer: &mut [u8]) -> Result<Block, Error> {
        let j0 = self.j0(nonce)?;
        // Check the lengths before encrypting anything.
        add_len(0, buffer.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        self.gctr(&j0, buffer);
        self.tag_of(&j0, aad, buffer)
    }

    /// GCM-AD (§7.2): if `tag` authenticates the ciphertext in `buffer` and
    /// `aad` under `nonce`, decrypts `buffer` in place. Otherwise returns an
    /// error and leaves `buffer` unchanged. `tag` may be truncated to 4, 8,
    /// 12, 13, 14 or 15 bytes (§5.2.1.2); callers must fix the length they
    /// accept rather than take it from the message.
    pub fn decrypt(
        &self,
        nonce: &[u8],
        aad: &[u8],
        buffer: &mut [u8],
        tag: &[u8],
    ) -> Result<(), Error> {
        let j0 = self.j0(nonce)?;
        verify(&self.tag_of(&j0, aad, buffer)?, tag)?;
        self.gctr(&j0, buffer);
        Ok(())
    }
}

/// Whether an [`AesGcmStream`] encrypts or decrypts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// Plaintext in, ciphertext out; [`AesGcmStream::finalize`] returns the
    /// tag.
    Encrypt,
    /// Ciphertext in, plaintext out; [`AesGcmStream::finalize`] checks the
    /// tag given to [`AesGcmStream::set_tag`].
    Decrypt,
}

/// An incremental AES-GCM encryption or decryption: the additional data
/// with [`update_aad`](Self::update_aad), then the text with
/// [`update`](Self::update), in pieces of any length.
///
/// **When decrypting, [`update`](Self::update) returns plaintext that has
/// not been authenticated yet.** Nothing may act on it before
/// [`finalize`](Self::finalize) has succeeded. When the whole message fits
/// in memory, [`AesGcm::decrypt`] checks the tag before it decrypts.
#[derive(Clone)]
pub struct AesGcmStream {
    key: AesGcm,
    direction: Direction,
    j0: Block,
    /// The next counter block.
    counter: Block,
    /// The keystream of the last counter block…
    keystream: Block,
    /// …of which this many bytes have been used.
    used: usize,
    /// GHASH of the blocks absorbed so far.
    y: Block,
    /// The bytes of a partial block not yet absorbed into `y`.
    pending: Block,
    pending_len: usize,
    aad_len: u64,
    text_len: u64,
    /// Whether [`update`](Self::update) has been called.
    in_text: bool,
    /// The tag from [`set_tag`](Self::set_tag).
    tag: Option<(Block, usize)>,
}

impl Drop for AesGcmStream {
    /// Wipes the keystream, the partial block of text and the GHASH state
    /// (the key wipes itself).
    fn drop(&mut self) {
        zeroize(&mut self.keystream);
        zeroize(&mut self.pending);
        zeroize(&mut self.y);
    }
}

impl AesGcmStream {
    /// Starts encrypting or decrypting a message under `key` (16, 24 or 32
    /// bytes long) and `nonce` (of any nonzero length; 12 bytes is the
    /// recommended one). A nonce must never be used twice with the same key.
    pub fn new(key: &[u8], nonce: &[u8], direction: Direction) -> Result<Self, Error> {
        let key = AesGcm::new(key)?;
        let j0 = key.j0(nonce)?;
        let mut counter = j0;
        let c = u32::from_be_bytes(counter[12..].try_into().unwrap()).wrapping_add(1);
        counter[12..].copy_from_slice(&c.to_be_bytes());
        Ok(AesGcmStream {
            key,
            direction,
            j0,
            counter,
            keystream: [0; 16],
            used: 16,
            y: [0; 16],
            pending: [0; 16],
            pending_len: 0,
            aad_len: 0,
            text_len: 0,
            in_text: false,
            tag: None,
        })
    }

    /// Absorbs `data` into GHASH, keeping a trailing partial block for later.
    fn absorb(&mut self, mut data: &[u8]) {
        if self.pending_len > 0 {
            let n = data.len().min(16 - self.pending_len);
            self.pending[self.pending_len..self.pending_len + n].copy_from_slice(&data[..n]);
            self.pending_len += n;
            data = &data[n..];
            if self.pending_len < 16 {
                return;
            }
            self.key.ghash(&mut self.y, &self.pending);
            self.pending_len = 0;
        }
        let whole = data.len() / 16 * 16;
        self.key.ghash(&mut self.y, &data[..whole]);
        self.pending[..data.len() - whole].copy_from_slice(&data[whole..]);
        self.pending_len = data.len() - whole;
    }

    /// Absorbs the partial block, padded with zeros.
    fn flush(&mut self) {
        self.key
            .ghash(&mut self.y, &self.pending[..self.pending_len]);
        self.pending_len = 0;
    }

    /// XORs the next `data.len()` bytes of keystream into `data`.
    fn crypt(&mut self, data: &mut [u8]) {
        let n = data.len().min(16 - self.used);
        let (head, data) = data.split_at_mut(n);
        for (d, k) in head.iter_mut().zip(&self.keystream[self.used..]) {
            *d ^= k;
        }
        self.used += n;
        let (blocks, rest) = data.as_chunks_mut::<16>();
        self.key.ctr32(&mut self.counter, blocks);
        if !rest.is_empty() {
            let mut ks = [[0u8; 16]];
            self.key.ctr32(&mut self.counter, &mut ks);
            self.keystream = ks[0];
            for (d, k) in rest.iter_mut().zip(&self.keystream) {
                *d ^= k;
            }
            self.used = rest.len();
        }
    }

    /// Absorbs more additional data. All of it must come before the text.
    pub fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        if self.in_text {
            return Err(Error::AadAfterText);
        }
        self.aad_len =
            add_len(self.aad_len, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        self.absorb(aad);
        Ok(())
    }

    /// Encrypts or decrypts the next `data.len()` bytes of the text in place.
    /// When decrypting, the result is not authenticated until
    /// [`finalize`](Self::finalize) succeeds.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        self.text_len =
            add_len(self.text_len, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        if !self.in_text {
            self.flush();
            self.in_text = true;
        }
        match self.direction {
            Direction::Encrypt => {
                self.crypt(data);
                self.absorb(data);
            }
            Direction::Decrypt => {
                self.absorb(data);
                self.crypt(data);
            }
        }
        Ok(())
    }

    /// Sets the tag that decryption must end with: 16 bytes, or truncated to
    /// 4, 8, 12, 13, 14 or 15 (§5.2.1.2). Callers must fix the length they
    /// accept rather than take it from the message.
    pub fn set_tag(&mut self, tag: &[u8]) -> Result<(), Error> {
        if self.direction == Direction::Encrypt {
            return Err(Error::TagWhenEncrypting);
        }
        if !TAG_LENGTHS.contains(&tag.len()) {
            return Err(Error::InvalidTagLength);
        }
        let mut t = [0u8; 16];
        t[..tag.len()].copy_from_slice(tag);
        self.tag = Some((t, tag.len()));
        Ok(())
    }

    /// Finishes the message and returns its full 16-byte tag. When
    /// decrypting, this first checks it against the tag given to
    /// [`set_tag`](Self::set_tag), and fails if they differ. GCM leaves no
    /// buffered text to return.
    pub fn finalize(mut self) -> Result<Block, Error> {
        self.flush();
        let tag = self.key.tag(&self.j0, self.y, self.aad_len, self.text_len);
        if self.direction == Direction::Decrypt {
            let (expected, len) = self.tag.ok_or(Error::MissingTag)?;
            verify(&tag, &expected[..len])?;
        }
        Ok(tag)
    }
}

#[cfg(test)]
mod tests {
    use super::{AesGcm, AesGcmStream, Backend, Direction, Error, MAX_AAD, MAX_TEXT, add_len};
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    use crate::cpu::Features;
    use crate::cpu::detected;

    /// The implementation chosen for each set of features.
    #[test]
    fn select() {
        #[cfg(target_arch = "x86_64")]
        {
            let all = Features::of(&["aes", "pclmulqdq", "ssse3"]);
            assert_eq!(Backend::select(all), Backend::AesNi);
            for f in [
                Features::of(&["aes", "ssse3"]),
                Features::of(&["pclmulqdq", "ssse3"]),
            ] {
                assert_eq!(Backend::select(f), Backend::Scalar);
            }
        }
        #[cfg(target_arch = "aarch64")]
        {
            assert_eq!(Backend::select(Features::of(&["aes"])), Backend::ArmCrypto);
            assert_eq!(Backend::select(Features(0)), Backend::Scalar);
        }
        let best = AesGcm::new(&[0; 16]).unwrap().backend;
        assert_eq!(best, Backend::select(detected()));
    }

    /// Encryption and decryption are inverse, for every key size, 12-byte
    /// and other nonces, and texts and additional data of whole and partial
    /// blocks; a truncated tag is accepted and a modified one is not.
    #[test]
    fn round_trip() {
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let msg: [u8; 67] = core::array::from_fn(|i| (i as u8).wrapping_mul(7));
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&key[..key_len]).unwrap();
            for nonce_len in [1, 12, 16, 17] {
                let nonce = &[0x5a; 17][..nonce_len];
                for len in [0, 1, 16, 31, 64, 67] {
                    let (msg, aad) = (&msg[..len], &msg[..len / 2]);
                    let mut buf = [0u8; 67];
                    let buf = &mut buf[..len];
                    buf.copy_from_slice(msg);
                    let tag = k.encrypt(nonce, aad, buf).unwrap();
                    assert!(len == 0 || buf != msg);
                    let mut bad = tag;
                    bad[15] ^= 1;
                    assert_eq!(k.decrypt(nonce, aad, buf, &bad), Err(Error::TagMismatch));
                    k.decrypt(nonce, aad, buf, &tag[..12]).unwrap();
                    assert_eq!(buf, msg);
                }
            }
        }
    }

    /// Streaming, with the additional data or the text split at every
    /// point (around block boundaries), agrees with the one-shot functions,
    /// in both directions.
    #[test]
    fn stream() {
        let key = [7u8; 16];
        let nonce = [9u8; 12];
        let aad: [u8; 40] = core::array::from_fn(|i| i as u8);
        let msg: [u8; 50] = core::array::from_fn(|i| (i as u8).wrapping_mul(13));
        let k = AesGcm::new(&key).unwrap();
        let mut ct = msg;
        let tag = k.encrypt(&nonce, &aad, &mut ct).unwrap();
        // Every split of one, with the other split in the middle.
        let splits = (0..=aad.len())
            .map(|a| (a, msg.len() / 2))
            .chain((0..=msg.len()).map(|m| (aad.len() / 2, m)));
        for (a, m) in splits {
            let mut e = AesGcmStream::new(&key, &nonce, Direction::Encrypt).unwrap();
            e.update_aad(&aad[..a]).unwrap();
            e.update_aad(&aad[a..]).unwrap();
            let mut buf = msg;
            let (x, y) = buf.split_at_mut(m);
            e.update(x).unwrap();
            e.update(y).unwrap();
            assert_eq!(buf, ct);
            assert_eq!(e.finalize(), Ok(tag));

            let mut d = AesGcmStream::new(&key, &nonce, Direction::Decrypt).unwrap();
            d.update_aad(&aad[..a]).unwrap();
            d.update_aad(&aad[a..]).unwrap();
            let (x, y) = buf.split_at_mut(m);
            d.update(x).unwrap();
            d.update(y).unwrap();
            assert_eq!(buf, msg);
            d.set_tag(&tag[..8]).unwrap();
            assert_eq!(d.finalize(), Ok(tag));
        }
        // A byte at a time.
        let mut e = AesGcmStream::new(&key, &nonce, Direction::Encrypt).unwrap();
        for b in aad.chunks(1) {
            e.update_aad(b).unwrap();
        }
        let mut buf = msg;
        for b in buf.chunks_mut(1) {
            e.update(b).unwrap();
        }
        assert_eq!(buf, ct);
        assert_eq!(e.finalize(), Ok(tag));
        // Without text, or without either.
        let mut t = [0u8; 0];
        let tag = k.encrypt(&nonce, &aad[..5], &mut t).unwrap();
        let mut e = AesGcmStream::new(&key, &nonce, Direction::Encrypt).unwrap();
        e.update_aad(&aad[..5]).unwrap();
        assert_eq!(e.finalize(), Ok(tag));
        let tag = k.encrypt(&nonce, &[], &mut t).unwrap();
        let e = AesGcmStream::new(&key, &nonce, Direction::Encrypt).unwrap();
        assert_eq!(e.finalize(), Ok(tag));
    }

    #[test]
    fn errors() {
        assert_eq!(AesGcm::new(&[0; 15]).err(), Some(Error::InvalidKeyLength));
        let k = AesGcm::new(&[0; 32]).unwrap();
        let mut buf = [0u8; 3];
        assert_eq!(
            k.encrypt(&[], &[], &mut buf),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(
            k.decrypt(&[], &[], &mut buf, &[0; 16]),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(
            k.decrypt(&[0; 12], &[], &mut buf, &[0; 5]),
            Err(Error::InvalidTagLength)
        );
        assert_eq!(
            k.decrypt(&[0; 12], &[], &mut buf, &[0; 16]),
            Err(Error::TagMismatch)
        );
        assert_eq!(buf, [0; 3]);

        let new = |d| AesGcmStream::new(&[0; 16], &[0; 12], d).unwrap();
        assert_eq!(
            AesGcmStream::new(&[0; 17], &[0; 12], Direction::Encrypt).err(),
            Some(Error::InvalidKeyLength)
        );
        assert_eq!(
            AesGcmStream::new(&[0; 16], &[], Direction::Decrypt).err(),
            Some(Error::InvalidNonceLength)
        );
        let mut e = new(Direction::Encrypt);
        e.update(&mut buf).unwrap();
        assert_eq!(e.update_aad(&[1]), Err(Error::AadAfterText));
        assert_eq!(e.set_tag(&[0; 16]), Err(Error::TagWhenEncrypting));
        let mut d = new(Direction::Decrypt);
        assert_eq!(d.set_tag(&[0; 3]), Err(Error::InvalidTagLength));
        assert_eq!(d.clone().finalize(), Err(Error::MissingTag));
        d.set_tag(&[0; 16]).unwrap();
        assert_eq!(d.finalize(), Err(Error::TagMismatch));

        // The length limits (§5.2.1.1), which no test can reach with real
        // buffers.
        assert_eq!(add_len(MAX_TEXT - 1, 1, MAX_TEXT), Ok(MAX_TEXT));
        assert_eq!(add_len(MAX_TEXT, 1, MAX_TEXT), Err(()));
        assert_eq!(add_len(MAX_AAD, 0, MAX_AAD), Ok(MAX_AAD));
        assert_eq!(add_len(u64::MAX, 1, MAX_AAD), Err(()));
        let mut e = new(Direction::Encrypt);
        e.text_len = MAX_TEXT;
        assert_eq!(e.update(&mut buf), Err(Error::InvalidTextLength));
        e.aad_len = MAX_AAD;
        e.in_text = false;
        assert_eq!(e.update_aad(&[1]), Err(Error::InvalidAadLength));
    }
}
