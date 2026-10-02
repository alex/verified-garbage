//! AES-GCM (NIST SP 800-38D) with 128-, 192- and 256-bit AES keys.
//!
//! The whole AEAD is verified assembly: `vg_aes_gcm_init` (contract
//! `VG.Spec.Gcm.initContract`) writes the key context (the AES key schedule
//! and the hash subkey `H`), `vg_aes_gcm_seal` and `vg_aes_gcm_open`
//! (`sealContract`, `openContract`) are GCM-AE and GCM-AD (§7), and
//! `vg_aes_gcm_stream_init`, `_aad`, `_encrypt`, `_decrypt`, `_finish` and
//! `_verify` keep a streaming state (`VG.Spec.Gcm.StreamRepr`). `open` and
//! `verify` check the tag, in constant time, and `open` decrypts only if it
//! matches. This module checks the lengths of §5.2.1.1 and §5.2.1.2, which
//! the assembly does not, and holds the key context and the state.
//!
//! The functions are emitted once for each implementation of AES
//! (`vg_aes_expand_key` and `vg_aes_ctr32`) and of `vg_ghash` they call,
//! which have the same contracts: on x86-64, CPUs with AES-NI and SSSE3 run
//! the `_aesni` instances (with `vg_aes_ctr32_aesni`), CPUs with PCLMULQDQ
//! and SSSE3 the `_pclmul` ones (with `vg_ghash_pclmul`), and CPUs with all
//! three the `_aesni_pclmul` ones; likewise on x86, where AES-NI needs no
//! SSSE3; on AArch64, CPUs with the AES and PMULL
//! extensions (which Rust's `aes` feature stands for together) run the
//! `_aes_pmull` ones.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_AES_FEATURES, VG_AES_GCM_SEAL_AES_PMULL_FEATURES,
    VG_AES_GCM_SEAL_PMULL_FEATURES, vg_aes_gcm_init_aes, vg_aes_gcm_init_aes_pmull,
    vg_aes_gcm_init_pmull, vg_aes_gcm_open_aes, vg_aes_gcm_open_aes_pmull, vg_aes_gcm_open_pmull,
    vg_aes_gcm_seal_aes, vg_aes_gcm_seal_aes_pmull, vg_aes_gcm_seal_pmull,
    vg_aes_gcm_stream_aad_aes, vg_aes_gcm_stream_aad_aes_pmull, vg_aes_gcm_stream_aad_pmull,
    vg_aes_gcm_stream_decrypt_aes, vg_aes_gcm_stream_decrypt_aes_pmull,
    vg_aes_gcm_stream_decrypt_pmull, vg_aes_gcm_stream_encrypt_aes,
    vg_aes_gcm_stream_encrypt_aes_pmull, vg_aes_gcm_stream_encrypt_pmull,
    vg_aes_gcm_stream_finish_aes, vg_aes_gcm_stream_finish_aes_pmull,
    vg_aes_gcm_stream_finish_pmull, vg_aes_gcm_stream_init_aes, vg_aes_gcm_stream_init_aes_pmull,
    vg_aes_gcm_stream_init_pmull, vg_aes_gcm_stream_verify_aes, vg_aes_gcm_stream_verify_aes_pmull,
    vg_aes_gcm_stream_verify_pmull,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_AESNI_FEATURES, VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES,
    VG_AES_GCM_SEAL_PCLMUL_FEATURES, vg_aes_gcm_init_aesni, vg_aes_gcm_init_aesni_pclmul,
    vg_aes_gcm_init_pclmul, vg_aes_gcm_open_aesni, vg_aes_gcm_open_aesni_pclmul,
    vg_aes_gcm_open_pclmul, vg_aes_gcm_seal_aesni, vg_aes_gcm_seal_aesni_pclmul,
    vg_aes_gcm_seal_pclmul, vg_aes_gcm_stream_aad_aesni, vg_aes_gcm_stream_aad_aesni_pclmul,
    vg_aes_gcm_stream_aad_pclmul, vg_aes_gcm_stream_decrypt_aesni,
    vg_aes_gcm_stream_decrypt_aesni_pclmul, vg_aes_gcm_stream_decrypt_pclmul,
    vg_aes_gcm_stream_encrypt_aesni, vg_aes_gcm_stream_encrypt_aesni_pclmul,
    vg_aes_gcm_stream_encrypt_pclmul, vg_aes_gcm_stream_finish_aesni,
    vg_aes_gcm_stream_finish_aesni_pclmul, vg_aes_gcm_stream_finish_pclmul,
    vg_aes_gcm_stream_init_aesni, vg_aes_gcm_stream_init_aesni_pclmul,
    vg_aes_gcm_stream_init_pclmul, vg_aes_gcm_stream_verify_aesni,
    vg_aes_gcm_stream_verify_aesni_pclmul, vg_aes_gcm_stream_verify_pclmul,
};
use crate::arch::gcm::{
    vg_aes_gcm_init, vg_aes_gcm_open, vg_aes_gcm_seal, vg_aes_gcm_stream_aad,
    vg_aes_gcm_stream_decrypt, vg_aes_gcm_stream_encrypt, vg_aes_gcm_stream_finish,
    vg_aes_gcm_stream_init, vg_aes_gcm_stream_verify,
};
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

/// The implementations of AES and GHASH the functions called call: each
/// combination is an instance of every `vg_aes_gcm_*` function. (A product
/// of `crate::aes::Backend` and a GHASH backend would let a caller pair them
/// any way; one enum of the instances keeps every `match` exhaustive over
/// exactly the functions that exist.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Backend {
    /// The baseline ISA: `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`.
    Scalar,
    /// AES-NI for AES: the `_aesni` instances.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    AesNi,
    /// PCLMULQDQ for GHASH: the `_pclmul` instances.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    Pclmul,
    /// Both: the `_aesni_pclmul` instances.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    AesNiPclmul,
    /// The AES instructions for AES: the `_aes` instances.
    #[cfg(target_arch = "aarch64")]
    Aes,
    /// PMULL for GHASH: the `_pmull` instances.
    #[cfg(target_arch = "aarch64")]
    Pmull,
    /// Both: the `_aes_pmull` instances.
    #[cfg(target_arch = "aarch64")]
    AesPmull,
}

/// The instance of a function for `backend`: the baseline one, then those
/// for x86-64 (AES-NI, PCLMULQDQ, both) and AArch64 (AES, PMULL, both).
macro_rules! instance {
    ($backend:expr, $scalar:ident,
     x86_64: [$aesni:ident, $pclmul:ident, $aesni_pclmul:ident],
     aarch64: [$aes:ident, $pmull:ident, $aes_pmull:ident]) => {
        match $backend {
            Backend::Scalar => $scalar,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNi => $aesni,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::Pclmul => $pclmul,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNiPclmul => $aesni_pclmul,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
            #[cfg(target_arch = "aarch64")]
            Backend::Pmull => $pmull,
            #[cfg(target_arch = "aarch64")]
            Backend::AesPmull => $aes_pmull,
        }
    };
}

/// The features of the baseline ISA: none.
const BASELINE: &[&str] = &[];

impl Backend {
    /// Every implementation, best first.
    const ALL: &[Backend] = &[
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        Backend::AesNiPclmul,
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        Backend::AesNi,
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        Backend::Pclmul,
        #[cfg(target_arch = "aarch64")]
        Backend::AesPmull,
        #[cfg(target_arch = "aarch64")]
        Backend::Aes,
        #[cfg(target_arch = "aarch64")]
        Backend::Pmull,
        Backend::Scalar,
    ];

    /// The CPU features its instances need: `seal`'s, which include every
    /// other function's (see the tests).
    fn features(self) -> Features {
        Features::of(instance!(self, BASELINE,
            x86_64: [VG_AES_GCM_SEAL_AESNI_FEATURES, VG_AES_GCM_SEAL_PCLMUL_FEATURES,
                VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES],
            aarch64: [VG_AES_GCM_SEAL_AES_FEATURES, VG_AES_GCM_SEAL_PMULL_FEATURES,
                VG_AES_GCM_SEAL_AES_PMULL_FEATURES]))
    }
}

/// The best implementation a CPU with the features `f` can run. On AArch64,
/// Rust's `aes` feature stands for both the AES and the PMULL extensions,
/// so this never chooses `Aes` or `Pmull` there: they exist because every
/// implementation of a function reaches the functions built on it (see
/// CLAUDE.md), and the tests run them.
fn select(f: Features) -> Backend {
    let best = Backend::ALL.iter().find(|b| f.contains(b.features()));
    *best.unwrap_or(&Backend::Scalar)
}

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

/// Checks that a nonce is not empty (§5.2.1.1; it is shorter than `2^61`
/// bytes, as no buffer is that long).
fn check_nonce(nonce: &[u8]) -> Result<(), Error> {
    if nonce.is_empty() {
        return Err(Error::InvalidNonceLength);
    }
    Ok(())
}

/// Checks that a tag has a length §5.2.1.2 allows.
fn check_tag(tag: &[u8]) -> Result<(), Error> {
    if !TAG_LENGTHS.contains(&tag.len()) {
        return Err(Error::InvalidTagLength);
    }
    Ok(())
}

/// Writes `tag` to the first bytes of `work`, where `open` and
/// `stream_verify` take the received tag.
fn put_tag(work: &mut MaybeUninit<[u64; 320]>, tag: &[u8]) {
    let mut t = [0u8; 16];
    t[..tag.len()].copy_from_slice(tag);
    let w = work.as_mut_ptr().cast::<u64>();
    // SAFETY: `work` is valid for writes of 320 words.
    unsafe {
        w.write(u64::from_le_bytes(t[..8].try_into().unwrap()));
        w.add(1)
            .write(u64::from_le_bytes(t[8..].try_into().unwrap()));
    }
}

/// The first 16 bytes of `work`, where `seal`, `stream_finish` and
/// `stream_verify` write the tag.
///
/// # Safety
///
/// They must have been written.
unsafe fn tag_of(work: &MaybeUninit<[u64; 320]>) -> Block {
    let w = work.as_ptr().cast::<u64>();
    let mut tag = [0u8; 16];
    // SAFETY: the first two words are initialized (the caller's guarantee).
    unsafe {
        tag[..8].copy_from_slice(&w.read().to_le_bytes());
        tag[8..].copy_from_slice(&w.add(1).read().to_le_bytes());
    }
    tag
}

/// An AES-GCM key: its key context (the AES key schedule and the hash
/// subkey `H`). Its [`encrypt_in_place`](Self::encrypt_in_place) and
/// [`decrypt_in_place`](Self::decrypt_in_place) are the one-shot AEAD;
/// [`AesGcmStream`] encrypts or decrypts incrementally.
#[derive(Clone)]
pub struct AesGcm {
    /// The key context `vg_aes_gcm_init` writes (`VG.Spec.Gcm.KeyRepr`).
    ctx: [u64; 32],
    rounds: usize,
    /// The implementations of AES and GHASH the functions called call.
    backend: Backend,
}

impl Drop for AesGcm {
    /// Wipes the key context.
    fn drop(&mut self) {
        zeroize(&mut self.ctx);
    }
}

impl AesGcm {
    /// The size of a full tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Prepares `key`, which must be 16, 24 or 32 bytes long (AES-128,
    /// AES-192 or AES-256).
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        Self::with_backend(key, select(detected()))
    }

    /// `new`, with the implementation `backend`, which the CPU must be able
    /// to run.
    fn with_backend(key: &[u8], backend: Backend) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
        }
        let mut k = AesGcm {
            ctx: [0; 32],
            rounds: key.len() / 4 + 6,
            backend,
        };
        let init = instance!(k.backend, vg_aes_gcm_init,
            x86_64: [vg_aes_gcm_init_aesni, vg_aes_gcm_init_pclmul, vg_aes_gcm_init_aesni_pclmul],
            aarch64: [vg_aes_gcm_init_aes, vg_aes_gcm_init_pmull, vg_aes_gcm_init_aes_pmull]);
        let mut scratch = MaybeUninit::<[u64; 320]>::uninit();
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `k.ctx` and `scratch` are valid for reads and writes of
        // 256 and 2560 bytes. They are distinct objects, so no two overlap,
        // nor do they overlap anything on the stack, or wrap around the end
        // of the address space. The CPU has the features of the
        // implementation selected. `scratch` is uninitialized: it is only
        // working space, and the contract's result does not depend on what
        // it holds.
        unsafe { init(key.as_ptr(), key.len(), &mut k.ctx, scratch.as_mut_ptr()) };
        Ok(k)
    }

    /// GCM-AE (§7.1): encrypts `data` in place under `nonce`, and returns
    /// the 16-byte tag authenticating the ciphertext and `aad`. A caller that
    /// wants a shorter tag truncates it (keeping its first bytes).
    ///
    /// The nonce may have any nonzero length; 12 bytes is the recommended
    /// (and fastest) one. A nonce must never be used twice with the same key.
    pub fn encrypt_in_place(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<Block, Error> {
        // Check the lengths before encrypting anything.
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let seal = instance!(self.backend, vg_aes_gcm_seal,
            x86_64: [vg_aes_gcm_seal_aesni, vg_aes_gcm_seal_pclmul, vg_aes_gcm_seal_aesni_pclmul],
            aarch64: [vg_aes_gcm_seal_aes, vg_aes_gcm_seal_pmull, vg_aes_gcm_seal_aes_pmull]);
        let mut work = MaybeUninit::<[u64; 320]>::uninit();
        // SAFETY: `self.ctx` is the key context `vg_aes_gcm_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds (every implementation writes
        // the same one), valid for reads of 256 bytes; `nonce` and `aad` are
        // valid for reads and `data` for reads and writes of their lengths,
        // and `work` (a local: working space, but for the tag written to it)
        // for reads and writes of 2560 bytes. They are distinct objects
        // (`data` a unique borrow), so the writable ones overlap nothing
        // else, nor anything on the stack, and none wraps around the end of
        // the address space. The CPU has the features of the implementation
        // selected.
        unsafe {
            seal(
                &self.ctx,
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                work.as_mut_ptr(),
            )
        };
        // SAFETY: `seal` wrote the tag to the first 16 bytes of `work`.
        Ok(unsafe { tag_of(&work) })
    }

    /// GCM-AD (§7.2): if `tag` authenticates the ciphertext in `data` and
    /// `aad` under `nonce`, decrypts `data` in place. Otherwise returns an
    /// error and leaves `data` unchanged. `tag` may be truncated to 4, 8,
    /// 12, 13, 14 or 15 bytes (§5.2.1.2); callers must fix the length they
    /// accept rather than take it from the message.
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8],
    ) -> Result<(), Error> {
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        check_tag(tag)?;
        let open = instance!(self.backend, vg_aes_gcm_open,
            x86_64: [vg_aes_gcm_open_aesni, vg_aes_gcm_open_pclmul, vg_aes_gcm_open_aesni_pclmul],
            aarch64: [vg_aes_gcm_open_aes, vg_aes_gcm_open_pmull, vg_aes_gcm_open_aes_pmull]);
        let mut work = MaybeUninit::<[u64; 320]>::uninit();
        put_tag(&mut work, tag);
        // SAFETY: as in `encrypt_in_place`, with the received tag in the
        // first `tag.len()` bytes of `work`.
        let ok = unsafe {
            open(
                &self.ctx,
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                work.as_mut_ptr(),
                tag.len(),
            )
        };
        // `open`'s contract leaves `data` as it was unless it returns 1.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

/// Whether a streaming cipher encrypts or decrypts: an [`AesGcmStream`], or
/// an `rc2_cbc::Rc2Cbc` (`rc2_cbc` re-exports this type).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// Plaintext in, ciphertext out.
    Encrypt,
    /// Ciphertext in, plaintext out.
    Decrypt,
}

/// An incremental AES-GCM encryption or decryption: the additional data
/// with [`update_aad`](Self::update_aad), then the text with
/// [`update`](Self::update), in pieces of any length.
///
/// **When decrypting, [`update`](Self::update) returns plaintext that has
/// not been authenticated yet.** Nothing may act on it before
/// [`finalize`](Self::finalize) has succeeded. When the whole message fits
/// in memory, [`AesGcm::decrypt_in_place`] checks the tag before it
/// decrypts.
#[derive(Clone)]
pub struct AesGcmStream {
    key: AesGcm,
    direction: Direction,
    /// The streaming state `vg_aes_gcm_stream_init` writes and the other
    /// functions update (`VG.Spec.Gcm.StreamRepr`).
    state: [u64; 10],
    aad_len: u64,
    text_len: u64,
    /// Whether [`update`](Self::update) has been called.
    in_text: bool,
    /// The tag from [`set_tag`](Self::set_tag).
    tag: Option<(Block, usize)>,
}

impl Drop for AesGcmStream {
    /// Wipes the streaming state (the key wipes itself).
    fn drop(&mut self) {
        zeroize(&mut self.state);
    }
}

impl AesGcmStream {
    /// Starts encrypting or decrypting a message under `key` (16, 24 or 32
    /// bytes long) and `nonce` (of any nonzero length; 12 bytes is the
    /// recommended one). A nonce must never be used twice with the same key.
    ///
    /// When encrypting, [`finalize`](Self::finalize) returns the tag; when
    /// decrypting, it checks the tag given to [`set_tag`](Self::set_tag).
    pub fn new(key: &[u8], nonce: &[u8], direction: Direction) -> Result<Self, Error> {
        Self::with_key(AesGcm::new(key)?, nonce, direction)
    }

    /// `new`, with the key already prepared.
    fn with_key(key: AesGcm, nonce: &[u8], direction: Direction) -> Result<Self, Error> {
        check_nonce(nonce)?;
        let mut s = AesGcmStream {
            key,
            direction,
            state: [0; 10],
            aad_len: 0,
            text_len: 0,
            in_text: false,
            tag: None,
        };
        let init = instance!(s.key.backend, vg_aes_gcm_stream_init,
            x86_64: [vg_aes_gcm_stream_init_aesni, vg_aes_gcm_stream_init_pclmul,
                vg_aes_gcm_stream_init_aesni_pclmul],
            aarch64: [vg_aes_gcm_stream_init_aes, vg_aes_gcm_stream_init_pmull, vg_aes_gcm_stream_init_aes_pmull]);
        let mut scratch = MaybeUninit::<[u64; 320]>::uninit();
        // SAFETY: `s.key.ctx` is a key context (as in
        // `AesGcm::encrypt_in_place`), valid for reads of 256 bytes, `nonce`
        // for reads of `nonce.len()`, and `s.state` and `scratch`
        // (uninitialized working space, as in `AesGcm::new`) for reads and
        // writes of 80 and 2560. They are distinct objects, so the writable
        // ones overlap nothing else, nor anything on the stack, and none
        // wraps around. The CPU has the features of the implementation
        // selected.
        unsafe {
            init(
                &s.key.ctx,
                nonce.as_ptr(),
                nonce.len(),
                &mut s.state,
                scratch.as_mut_ptr(),
            )
        };
        Ok(s)
    }

    /// Absorbs more additional data. All of it must come before the text.
    pub fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        if self.in_text {
            return Err(Error::AadAfterText);
        }
        let aad_len =
            add_len(self.aad_len, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let f = instance!(self.key.backend, vg_aes_gcm_stream_aad,
            x86_64: [vg_aes_gcm_stream_aad_aesni, vg_aes_gcm_stream_aad_pclmul,
                vg_aes_gcm_stream_aad_aesni_pclmul],
            aarch64: [vg_aes_gcm_stream_aad_aes, vg_aes_gcm_stream_aad_pmull, vg_aes_gcm_stream_aad_aes_pmull]);
        let mut scratch = MaybeUninit::<[u64; 320]>::uninit();
        // SAFETY: as in `new`; `self.state` represents a message with
        // `self.aad_len` bytes of additional data and no text yet.
        unsafe {
            f(
                &self.key.ctx,
                &mut self.state,
                self.aad_len,
                aad.as_ptr(),
                aad.len(),
                scratch.as_mut_ptr(),
            )
        };
        self.aad_len = aad_len;
        Ok(())
    }

    /// Encrypts or decrypts the next `data.len()` bytes of the text in place.
    /// When decrypting, the result is not authenticated until
    /// [`finalize`](Self::finalize) succeeds.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        let text_len =
            add_len(self.text_len, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        self.in_text = true;
        let f = match self.direction {
            Direction::Encrypt => instance!(self.key.backend, vg_aes_gcm_stream_encrypt,
                x86_64: [vg_aes_gcm_stream_encrypt_aesni, vg_aes_gcm_stream_encrypt_pclmul,
                    vg_aes_gcm_stream_encrypt_aesni_pclmul],
                aarch64: [vg_aes_gcm_stream_encrypt_aes, vg_aes_gcm_stream_encrypt_pmull, vg_aes_gcm_stream_encrypt_aes_pmull]),
            Direction::Decrypt => instance!(self.key.backend, vg_aes_gcm_stream_decrypt,
                x86_64: [vg_aes_gcm_stream_decrypt_aesni, vg_aes_gcm_stream_decrypt_pclmul,
                    vg_aes_gcm_stream_decrypt_aesni_pclmul],
                aarch64: [vg_aes_gcm_stream_decrypt_aes, vg_aes_gcm_stream_decrypt_pmull, vg_aes_gcm_stream_decrypt_aes_pmull]),
        };
        let mut scratch = MaybeUninit::<[u64; 320]>::uninit();
        // SAFETY: as in `new`, with `data` valid for reads and writes of
        // `data.len()` bytes (a unique borrow, so it overlaps nothing else);
        // `self.state` represents a message with `self.aad_len` bytes of
        // additional data and `self.text_len` of text.
        unsafe {
            f(
                &self.key.ctx,
                self.key.rounds,
                &mut self.state,
                self.aad_len,
                self.text_len,
                data.as_mut_ptr(),
                data.len(),
                scratch.as_mut_ptr(),
            )
        };
        self.text_len = text_len;
        Ok(())
    }

    /// Sets the tag that decryption must end with: 16 bytes, or truncated to
    /// 4, 8, 12, 13, 14 or 15 (§5.2.1.2). Callers must fix the length they
    /// accept rather than take it from the message.
    pub fn set_tag(&mut self, tag: &[u8]) -> Result<(), Error> {
        if self.direction == Direction::Encrypt {
            return Err(Error::TagWhenEncrypting);
        }
        check_tag(tag)?;
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
        let mut work = MaybeUninit::<[u64; 320]>::uninit();
        match self.direction {
            Direction::Encrypt => {
                let f = instance!(self.key.backend, vg_aes_gcm_stream_finish,
                    x86_64: [vg_aes_gcm_stream_finish_aesni, vg_aes_gcm_stream_finish_pclmul,
                        vg_aes_gcm_stream_finish_aesni_pclmul],
                    aarch64: [vg_aes_gcm_stream_finish_aes, vg_aes_gcm_stream_finish_pmull, vg_aes_gcm_stream_finish_aes_pmull]);
                // SAFETY: as in `update`, with `work` (a local: working space,
                // but for the tag written to it) valid for reads and writes of
                // 2560 bytes.
                unsafe {
                    f(
                        &self.key.ctx,
                        self.key.rounds,
                        &mut self.state,
                        self.aad_len,
                        self.text_len,
                        work.as_mut_ptr(),
                    )
                };
            }
            Direction::Decrypt => {
                let (tag, len) = self.tag.ok_or(Error::MissingTag)?;
                put_tag(&mut work, &tag[..len]);
                let f = instance!(self.key.backend, vg_aes_gcm_stream_verify,
                    x86_64: [vg_aes_gcm_stream_verify_aesni, vg_aes_gcm_stream_verify_pclmul,
                        vg_aes_gcm_stream_verify_aesni_pclmul],
                    aarch64: [vg_aes_gcm_stream_verify_aes, vg_aes_gcm_stream_verify_pmull, vg_aes_gcm_stream_verify_aes_pmull]);
                // SAFETY: as for `vg_aes_gcm_stream_finish`, with the
                // received tag in the first `len` bytes of `work`.
                let ok = unsafe {
                    f(
                        &self.key.ctx,
                        self.key.rounds,
                        &mut self.state,
                        self.aad_len,
                        self.text_len,
                        work.as_mut_ptr(),
                        len,
                    )
                };
                if ok != 1 {
                    return Err(Error::TagMismatch);
                }
            }
        }
        // SAFETY: `stream_finish` and `stream_verify` (when it returns 1)
        // write the tag to the first 16 bytes of `work`.
        Ok(unsafe { tag_of(&work) })
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AesGcm, AesGcmStream, Backend, Direction, Error, MAX_AAD, MAX_TEXT, add_len, select,
    };
    use crate::cpu::{Features, detected};

    /// The implementation chosen for each set of features: AES's and
    /// GHASH's, independently.
    #[test]
    fn backend() {
        let f = |names: &[&str]| select(Features::of(names));
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            assert_eq!(f(&["aes", "pclmulqdq", "ssse3"]), Backend::AesNiPclmul);
            assert_eq!(f(&["aes", "ssse3"]), Backend::AesNi);
            assert_eq!(f(&["pclmulqdq", "ssse3"]), Backend::Pclmul);
        }
        // AES-NI needs SSSE3 too on x86-64 (`vg_aes_ctr32_aesni`'s byte
        // shuffles), not on x86.
        #[cfg(target_arch = "x86_64")]
        assert_eq!(f(&["aes", "pclmulqdq"]), Backend::Scalar);
        #[cfg(target_arch = "x86")]
        {
            assert_eq!(f(&["aes"]), Backend::AesNi);
            assert_eq!(f(&["aes", "pclmulqdq"]), Backend::AesNi);
        }
        #[cfg(target_arch = "aarch64")]
        assert_eq!(f(&["aes"]), Backend::AesPmull);
        assert_eq!(f(&[]), Backend::Scalar);
        let best = AesGcm::new(&[0; 16]).unwrap().backend;
        assert_eq!(best, select(detected()));
    }

    /// Every implementation this CPU can run, including those `select`
    /// never chooses (AArch64's `Aes` and `Pmull`), agrees with the
    /// baseline one, one-shot and streaming.
    #[test]
    fn instances() {
        let key = [3u8; 24];
        let nonce = [5u8; 13];
        let aad: [u8; 21] = core::array::from_fn(|i| i as u8);
        let msg: [u8; 37] = core::array::from_fn(|i| (i as u8).wrapping_mul(11));
        let base = AesGcm::with_backend(&key, Backend::Scalar).unwrap();
        let mut ct = msg;
        let tag = base.encrypt_in_place(&nonce, &aad, &mut ct).unwrap();
        for &b in Backend::ALL {
            if !detected().contains(b.features()) {
                continue;
            }
            let k = AesGcm::with_backend(&key, b).unwrap();
            let mut buf = msg;
            assert_eq!(k.encrypt_in_place(&nonce, &aad, &mut buf), Ok(tag));
            assert_eq!(buf, ct);
            assert_eq!(k.decrypt_in_place(&nonce, &aad, &mut buf, &tag), Ok(()));
            assert_eq!(buf, msg);
            for direction in [Direction::Encrypt, Direction::Decrypt] {
                let mut s = AesGcmStream::with_key(k.clone(), &nonce, direction).unwrap();
                s.update_aad(&aad[..7]).unwrap();
                s.update_aad(&aad[7..]).unwrap();
                let (x, y) = buf.split_at_mut(20);
                s.update(x).unwrap();
                s.update(y).unwrap();
                if direction == Direction::Decrypt {
                    s.set_tag(&tag).unwrap();
                }
                assert_eq!(s.finalize(), Ok(tag));
                assert_eq!(
                    buf,
                    if direction == Direction::Encrypt {
                        ct
                    } else {
                        msg
                    }
                );
            }
        }
    }

    /// Every function's instances need at most the features `seal`'s do,
    /// which `select` checks (`init` needs only AES's, `stream_init` and
    /// `stream_aad` only GHASH's).
    #[test]
    fn features() {
        #[cfg(target_arch = "x86")]
        {
            use crate::arch::gcm::*;
            let groups: [(&[&str], &[&[&str]]); 3] = [
                (
                    VG_AES_GCM_SEAL_AESNI_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_PCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_STREAM_AAD_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_PCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_PCLMUL_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_PCLMUL_FEATURES,
                    ][..],
                ),
            ];
            for (seal, others) in groups {
                for other in others {
                    assert!(Features::of(seal).contains(Features::of(other)));
                }
            }
        }
        #[cfg(target_arch = "x86_64")]
        {
            use crate::arch::gcm::*;
            let groups: [(&[&str], &[&[&str]]); 3] = [
                (
                    VG_AES_GCM_SEAL_AESNI_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_PCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_OPEN_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_PCLMUL_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_PCLMUL_FEATURES,
                    ][..],
                ),
            ];
            for (seal, others) in groups {
                for other in others {
                    assert!(Features::of(seal).contains(Features::of(other)));
                }
            }
        }
        #[cfg(target_arch = "aarch64")]
        {
            use crate::arch::gcm::*;
            let groups: [(&[&str], &[&[&str]]); 3] = [
                (
                    VG_AES_GCM_SEAL_AES_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AES_FEATURES,
                        VG_AES_GCM_OPEN_AES_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AES_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AES_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AES_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AES_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_PMULL_FEATURES,
                    &[
                        VG_AES_GCM_OPEN_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_PMULL_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_AES_PMULL_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AES_PMULL_FEATURES,
                        VG_AES_GCM_OPEN_AES_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_AES_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_AES_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AES_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AES_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AES_PMULL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AES_PMULL_FEATURES,
                    ][..],
                ),
            ];
            for (seal, others) in groups {
                for other in others {
                    assert!(Features::of(seal).contains(Features::of(other)));
                }
            }
        }
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
                    let tag = k.encrypt_in_place(nonce, aad, buf).unwrap();
                    assert!(len == 0 || buf != msg);
                    let mut bad = tag;
                    bad[15] ^= 1;
                    assert_eq!(
                        k.decrypt_in_place(nonce, aad, buf, &bad),
                        Err(Error::TagMismatch)
                    );
                    k.decrypt_in_place(nonce, aad, buf, &tag[..12]).unwrap();
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
        let tag = k.encrypt_in_place(&nonce, &aad, &mut ct).unwrap();
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
        let tag = k.encrypt_in_place(&nonce, &aad[..5], &mut t).unwrap();
        let mut e = AesGcmStream::new(&key, &nonce, Direction::Encrypt).unwrap();
        e.update_aad(&aad[..5]).unwrap();
        assert_eq!(e.finalize(), Ok(tag));
        let tag = k.encrypt_in_place(&nonce, &[], &mut t).unwrap();
        let e = AesGcmStream::new(&key, &nonce, Direction::Encrypt).unwrap();
        assert_eq!(e.finalize(), Ok(tag));
    }

    #[test]
    fn errors() {
        assert_eq!(AesGcm::new(&[0; 15]).err(), Some(Error::InvalidKeyLength));
        let k = AesGcm::new(&[0; 32]).unwrap();
        let mut buf = [0u8; 3];
        assert_eq!(
            k.encrypt_in_place(&[], &[], &mut buf),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(
            k.decrypt_in_place(&[], &[], &mut buf, &[0; 16]),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(
            k.decrypt_in_place(&[0; 12], &[], &mut buf, &[0; 5]),
            Err(Error::InvalidTagLength)
        );
        assert_eq!(
            k.decrypt_in_place(&[0; 12], &[], &mut buf, &[0; 16]),
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
