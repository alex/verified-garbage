//! AES-GCM (NIST SP 800-38D) with 128-, 192- and 256-bit AES keys.
//!
//! The whole AEAD is verified assembly: `vg_aes_gcm_init` (contract
//! `VG.Spec.Gcm.initContract`) writes the key context (the AES key schedule
//! and the hash subkey `H`), `vg_aes_gcm_seal` and `vg_aes_gcm_open`
//! (`sealContract`, `openContract`) are GCM-AE and GCM-AD (§7), and
//! `vg_aes_gcm_stream_init`, `_aad`, `_encrypt`, `_decrypt`, `_finish` and
//! `_verify` keep a streaming state (`VG.Spec.Gcm.StreamRepr`). `open` and
//! `verify` check the tag, in constant time, and `open` decrypts only if it
//! matches. This module checks the lengths of §5.2.1.1, which the assembly
//! does not, and holds the key context and the state.
//!
//! An [`AesGcm`] is a key: it encrypts and decrypts whole messages at once,
//! and starts incremental ones with [`AesGcm::encryptor`] and
//! [`AesGcm::decryptor`], which borrow it. **An [`AesGcmDecryptor`]'s
//! `update` returns plaintext that has not been authenticated yet**: nothing
//! may act on it before its `finalize` has succeeded. When the whole message
//! fits in memory, [`AesGcm::decrypt_in_place`] checks the tag before it
//! decrypts.
//!
//! # Tags
//!
//! Encryption returns the full 16-byte tag; a protocol that sends a shorter
//! one sends its first bytes. Decryption takes a `&[u8; 16]`
//! ([`AesGcm::decrypt_in_place`], [`AesGcmDecryptor::finalize`]), or, for a
//! protocol that truncates the tag, a `&[u8; N]` whose length `N` is a type
//! parameter ([`AesGcm::decrypt_in_place_truncated`],
//! [`AesGcmDecryptor::finalize_truncated`]): one of the lengths SP 800-38D
//! §5.2.1.2 allows, 4, 8, 12, 13, 14, 15 or 16 bytes, checked at compile
//! time. The length is never taken from a slice, because a slice's length
//! often comes from the message: a protocol that splits a message with
//! `msg.split_at(msg.len().saturating_sub(16))` would, given a 4-byte
//! message, check an empty ciphertext against a 4-byte tag, which an
//! attacker forges with probability 2⁻³² instead of 2⁻¹²⁸. Tags of 4 and 8
//! bytes are only for the applications of SP 800-38D Appendix C, which
//! bounds the lengths of the messages and the number of decryptions under
//! one key.
//!
//! The functions are emitted once for each implementation of AES
//! (`vg_aes_expand_key` and `vg_aes_ctr32`) and of `vg_ghash` they call,
//! which have the same contracts: on x86-64, CPUs with AES-NI and SSSE3 run
//! the `_aesni` instances (with `vg_aes_ctr32_aesni`), CPUs with PCLMULQDQ
//! and SSSE3 the `_pclmul` ones (with `vg_ghash_pclmul`), and CPUs with all
//! three the `_aesni_pclmul` ones; likewise on x86, where AES-NI needs no
//! SSSE3; on AArch64, CPUs with the AES and PMULL extensions (which Rust's
//! `aes` feature stands for together) run the `_aes` ones (with
//! `vg_aes_ctr32_aes` and `vg_ghash_aes`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_AES_FEATURES, vg_aes_gcm_init_aes, vg_aes_gcm_open_aes, vg_aes_gcm_seal_aes,
    vg_aes_gcm_stream_aad_aes, vg_aes_gcm_stream_decrypt_aes, vg_aes_gcm_stream_encrypt_aes,
    vg_aes_gcm_stream_finish_aes, vg_aes_gcm_stream_init_aes, vg_aes_gcm_stream_verify_aes,
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
    /// The AES instructions for AES and PMULL for GHASH (Rust's `aes`
    /// feature stands for both): the `_aes` instances.
    #[cfg(target_arch = "aarch64")]
    Aes,
}

/// The instance of a function for `backend`: the baseline one, then those
/// for x86-64 and x86 (AES-NI, PCLMULQDQ, both) and AArch64 (AES and PMULL).
macro_rules! instance {
    ($backend:expr, $scalar:ident,
     x86_64: [$aesni:ident, $pclmul:ident, $aesni_pclmul:ident],
     aarch64: [$aes:ident]) => {
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
        Backend::Aes,
        Backend::Scalar,
    ];

    /// The CPU features its instances need: `seal`'s, which include every
    /// other function's (see the tests).
    fn features(self) -> Features {
        Features::of(instance!(self, BASELINE,
            x86_64: [VG_AES_GCM_SEAL_AESNI_FEATURES, VG_AES_GCM_SEAL_PCLMUL_FEATURES,
                VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES],
            aarch64: [VG_AES_GCM_SEAL_AES_FEATURES]))
    }
}

/// The best implementation a CPU with the features `f` can run.
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
    /// The tag does not match: the ciphertext, the additional data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
    /// [`AesGcmEncryptor::update_aad`] or [`AesGcmDecryptor::update_aad`]
    /// was called after `update`: GCM authenticates all of the additional
    /// data before the text.
    AadAfterText,
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

/// Fails to compile unless `N` is a tag length §5.2.1.2 allows: 4, 8, 12,
/// 13, 14, 15 or 16 bytes.
macro_rules! assert_tag_length {
    ($n:expr) => {
        const {
            assert!(
                matches!($n, 4 | 8 | 12 | 13 | 14 | 15 | 16),
                "an AES-GCM tag is 4, 8, 12, 13, 14, 15 or 16 bytes long"
            )
        }
    };
}

/// Writes `tag` (at most 16 bytes) to the first bytes of `work`, where
/// `open` and `stream_verify` take the received tag.
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
/// [`decrypt_in_place`](Self::decrypt_in_place) (or
/// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated)) are the
/// one-shot AEAD; [`encryptor`](Self::encryptor) and
/// [`decryptor`](Self::decryptor) start incremental ones.
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
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
        }
        let mut k = AesGcm {
            ctx: [0; 32],
            rounds: key.len() / 4 + 6,
            backend: select(detected()),
        };
        let init = instance!(k.backend, vg_aes_gcm_init,
            x86_64: [vg_aes_gcm_init_aesni, vg_aes_gcm_init_pclmul, vg_aes_gcm_init_aesni_pclmul],
            aarch64: [vg_aes_gcm_init_aes]);
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
    /// wants a shorter tag truncates it (keeping its first bytes), and
    /// decrypts with [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated).
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
            aarch64: [vg_aes_gcm_seal_aes]);
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

    /// GCM-AD (§7.2): if the 16-byte `tag` authenticates the ciphertext in
    /// `data` and `aad` under `nonce`, decrypts `data` in place. Otherwise
    /// returns an error and leaves `data` unchanged.
    ///
    /// A protocol that truncates the tag uses
    /// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated).
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        self.decrypt_in_place_truncated(nonce, aad, data, tag)
    }

    /// GCM-AD (§7.2) with a tag truncated to `N` bytes: if `tag` is the
    /// first `N` bytes of the tag of the ciphertext in `data` and `aad` under
    /// `nonce`, decrypts `data` in place. Otherwise returns an error and
    /// leaves `data` unchanged.
    ///
    /// `N` must be 4, 8, 12, 13, 14, 15 or 16 (SP 800-38D §5.2.1.2); any
    /// other length is an error when the call is compiled. It is a type parameter, fixed
    /// in the caller's code, so that it cannot come from the message: see
    /// the [module documentation](self#tags). SP 800-38D Appendix C
    /// restricts 4- and 8-byte tags to applications that bound the length of
    /// the messages and the number of decryptions under one key.
    pub fn decrypt_in_place_truncated<const N: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; N],
    ) -> Result<(), Error> {
        assert_tag_length!(N);
        self.open(nonce, aad, data, tag)
    }

    /// GCM-AD (§7.2) with `tag`, of a length §5.2.1.2 allows (which the
    /// callers check at compile time; `vg_aes_gcm_open` rejects any other).
    fn open(&self, nonce: &[u8], aad: &[u8], data: &mut [u8], tag: &[u8]) -> Result<(), Error> {
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let open = instance!(self.backend, vg_aes_gcm_open,
            x86_64: [vg_aes_gcm_open_aesni, vg_aes_gcm_open_pclmul, vg_aes_gcm_open_aesni_pclmul],
            aarch64: [vg_aes_gcm_open_aes]);
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

    /// Starts encrypting a message under this key and `nonce` (of any
    /// nonzero length; 12 bytes is the recommended one). A nonce must never
    /// be used twice with the same key.
    pub fn encryptor(&self, nonce: &[u8]) -> Result<AesGcmEncryptor<'_>, Error> {
        Ok(AesGcmEncryptor {
            stream: Stream::new(self, nonce)?,
        })
    }

    /// Starts decrypting a message under this key and `nonce`. Its
    /// [`update`](AesGcmDecryptor::update) returns plaintext that has not
    /// been authenticated until its [`finalize`](AesGcmDecryptor::finalize)
    /// succeeds.
    pub fn decryptor(&self, nonce: &[u8]) -> Result<AesGcmDecryptor<'_>, Error> {
        Ok(AesGcmDecryptor {
            stream: Stream::new(self, nonce)?,
        })
    }
}

/// The state of an incremental encryption or decryption (`DECRYPT`), which
/// [`AesGcmEncryptor`] and [`AesGcmDecryptor`] wrap: the key, the streaming
/// state, and the lengths absorbed so far.
#[derive(Clone)]
struct Stream<'a, const DECRYPT: bool> {
    key: &'a AesGcm,
    /// The streaming state `vg_aes_gcm_stream_init` writes and the other
    /// functions update (`VG.Spec.Gcm.StreamRepr`).
    state: [u64; 10],
    aad_len: u64,
    text_len: u64,
    /// Whether [`update`](Self::update) has been called.
    in_text: bool,
}

impl<const DECRYPT: bool> Drop for Stream<'_, DECRYPT> {
    /// Wipes the streaming state (the key wipes itself).
    fn drop(&mut self) {
        zeroize(&mut self.state);
    }
}

impl<'a, const DECRYPT: bool> Stream<'a, DECRYPT> {
    /// Starts a message under `key` and `nonce`.
    fn new(key: &'a AesGcm, nonce: &[u8]) -> Result<Self, Error> {
        check_nonce(nonce)?;
        let mut s = Stream {
            key,
            state: [0; 10],
            aad_len: 0,
            text_len: 0,
            in_text: false,
        };
        let init = instance!(key.backend, vg_aes_gcm_stream_init,
            x86_64: [vg_aes_gcm_stream_init_aesni, vg_aes_gcm_stream_init_pclmul,
                vg_aes_gcm_stream_init_aesni_pclmul],
            aarch64: [vg_aes_gcm_stream_init_aes]);
        let mut scratch = MaybeUninit::<[u64; 320]>::uninit();
        // SAFETY: `key.ctx` is a key context (as in
        // `AesGcm::encrypt_in_place`), valid for reads of 256 bytes, `nonce`
        // for reads of `nonce.len()`, and `s.state` and `scratch`
        // (uninitialized working space, as in `AesGcm::new`) for reads and
        // writes of 80 and 2560. They are distinct objects, so the writable
        // ones overlap nothing else, nor anything on the stack, and none
        // wraps around. The CPU has the features of the implementation
        // selected.
        unsafe {
            init(
                &key.ctx,
                nonce.as_ptr(),
                nonce.len(),
                &mut s.state,
                scratch.as_mut_ptr(),
            )
        };
        Ok(s)
    }

    /// Absorbs more additional data, which must all come before the text.
    fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        if self.in_text {
            return Err(Error::AadAfterText);
        }
        let aad_len =
            add_len(self.aad_len, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let f = instance!(self.key.backend, vg_aes_gcm_stream_aad,
            x86_64: [vg_aes_gcm_stream_aad_aesni, vg_aes_gcm_stream_aad_pclmul,
                vg_aes_gcm_stream_aad_aesni_pclmul],
            aarch64: [vg_aes_gcm_stream_aad_aes]);
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

    /// Encrypts (or, if `DECRYPT`, decrypts) the next `data.len()` bytes of
    /// the text in place.
    fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        let text_len =
            add_len(self.text_len, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        self.in_text = true;
        let f = if DECRYPT {
            instance!(self.key.backend, vg_aes_gcm_stream_decrypt,
                x86_64: [vg_aes_gcm_stream_decrypt_aesni, vg_aes_gcm_stream_decrypt_pclmul,
                    vg_aes_gcm_stream_decrypt_aesni_pclmul],
                aarch64: [vg_aes_gcm_stream_decrypt_aes])
        } else {
            instance!(self.key.backend, vg_aes_gcm_stream_encrypt,
                x86_64: [vg_aes_gcm_stream_encrypt_aesni, vg_aes_gcm_stream_encrypt_pclmul,
                    vg_aes_gcm_stream_encrypt_aesni_pclmul],
                aarch64: [vg_aes_gcm_stream_encrypt_aes])
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
}

impl Stream<'_, false> {
    /// Finishes the message and returns its 16-byte tag.
    fn finish(mut self) -> Block {
        let f = instance!(self.key.backend, vg_aes_gcm_stream_finish,
            x86_64: [vg_aes_gcm_stream_finish_aesni, vg_aes_gcm_stream_finish_pclmul,
                vg_aes_gcm_stream_finish_aesni_pclmul],
            aarch64: [vg_aes_gcm_stream_finish_aes]);
        let mut work = MaybeUninit::<[u64; 320]>::uninit();
        // SAFETY: as in `update`, with `work` (a local: working space, but
        // for the tag written to it) valid for reads and writes of 2560
        // bytes. `update_aad` and `update` checked the lengths (§5.2.1.1).
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
        // SAFETY: `stream_finish` wrote the tag to the first 16 bytes of
        // `work`.
        unsafe { tag_of(&work) }
    }
}

impl Stream<'_, true> {
    /// Finishes the message and checks that `tag` (of a length §5.2.1.2
    /// allows, which the callers check at compile time;
    /// `vg_aes_gcm_stream_verify` rejects any other) is the first
    /// `tag.len()` bytes of its tag.
    fn verify(mut self, tag: &[u8]) -> Result<(), Error> {
        let f = instance!(self.key.backend, vg_aes_gcm_stream_verify,
            x86_64: [vg_aes_gcm_stream_verify_aesni, vg_aes_gcm_stream_verify_pclmul,
                vg_aes_gcm_stream_verify_aesni_pclmul],
            aarch64: [vg_aes_gcm_stream_verify_aes]);
        let mut work = MaybeUninit::<[u64; 320]>::uninit();
        put_tag(&mut work, tag);
        // SAFETY: as in `finish`, with the received tag in the first
        // `tag.len()` bytes of `work`.
        let ok = unsafe {
            f(
                &self.key.ctx,
                self.key.rounds,
                &mut self.state,
                self.aad_len,
                self.text_len,
                work.as_mut_ptr(),
                tag.len(),
            )
        };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

/// An incremental AES-GCM encryption, from [`AesGcm::encryptor`]: the
/// additional data with [`update_aad`](Self::update_aad), then the plaintext
/// with [`update`](Self::update), in pieces of any length, and the tag from
/// [`finalize`](Self::finalize).
///
/// It borrows its [`AesGcm`], so a key encrypts many messages without
/// expanding it again.
#[derive(Clone)]
pub struct AesGcmEncryptor<'a> {
    stream: Stream<'a, false>,
}

impl AesGcmEncryptor<'_> {
    /// Absorbs more additional data. All of it must come before the
    /// plaintext.
    pub fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        self.stream.update_aad(aad)
    }

    /// Encrypts the next `data.len()` bytes of the plaintext in place.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        self.stream.update(data)
    }

    /// Finishes the message and returns its full 16-byte tag. A protocol
    /// that sends a shorter tag sends its first bytes. GCM leaves no
    /// buffered text to return.
    pub fn finalize(self) -> Block {
        self.stream.finish()
    }
}

/// An incremental AES-GCM decryption, from [`AesGcm::decryptor`]: the
/// additional data with [`update_aad`](Self::update_aad), then the
/// ciphertext with [`update`](Self::update), in pieces of any length, and
/// the tag checked by [`finalize`](Self::finalize) (16 bytes) or
/// [`finalize_truncated`](Self::finalize_truncated) (a length fixed at
/// compile time: see the [module documentation](self#tags)).
///
/// **[`update`](Self::update) returns plaintext that has not been
/// authenticated yet.** Nothing may act on it before
/// [`finalize`](Self::finalize) (or
/// [`finalize_truncated`](Self::finalize_truncated)) has succeeded. When the
/// whole message fits in memory, [`AesGcm::decrypt_in_place`] checks the tag
/// before it decrypts.
#[derive(Clone)]
pub struct AesGcmDecryptor<'a> {
    stream: Stream<'a, true>,
}

impl AesGcmDecryptor<'_> {
    /// Absorbs more additional data. All of it must come before the
    /// ciphertext.
    pub fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        self.stream.update_aad(aad)
    }

    /// Decrypts the next `data.len()` bytes of the ciphertext in place. The
    /// result is not authenticated until [`finalize`](Self::finalize) (or
    /// [`finalize_truncated`](Self::finalize_truncated)) succeeds.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        self.stream.update(data)
    }

    /// Finishes the message and checks that `tag` is its 16-byte tag. If
    /// they differ, this fails, and nothing may act on the plaintext
    /// [`update`](Self::update) returned.
    ///
    /// A protocol that truncates the tag uses
    /// [`finalize_truncated`](Self::finalize_truncated).
    pub fn finalize(self, tag: &[u8; 16]) -> Result<(), Error> {
        self.finalize_truncated(tag)
    }

    /// Finishes the message and checks that `tag` is the first `N` bytes of
    /// its tag. If they differ, this fails, and nothing may act on the
    /// plaintext [`update`](Self::update) returned.
    ///
    /// `N` must be 4, 8, 12, 13, 14, 15 or 16 (SP 800-38D §5.2.1.2); any
    /// other length is an error when the call is compiled. It is a type
    /// parameter, fixed in the caller's code, so that it cannot come from the
    /// message: see the [module documentation](self#tags). SP 800-38D
    /// Appendix C restricts 4- and 8-byte tags to applications that bound the
    /// length of the messages and the number of decryptions under one key.
    pub fn finalize_truncated<const N: usize>(self, tag: &[u8; N]) -> Result<(), Error> {
        assert_tag_length!(N);
        self.stream.verify(tag)
    }
}

#[cfg(test)]
mod tests {
    use super::{AesGcm, Backend, Error, MAX_AAD, MAX_TEXT, add_len, select};
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
        assert_eq!(f(&["aes"]), Backend::Aes);
        assert_eq!(f(&[]), Backend::Scalar);
        let best = AesGcm::new(&[0; 16]).unwrap().backend;
        assert_eq!(best, select(detected()));
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
            for other in [
                VG_AES_GCM_INIT_AES_FEATURES,
                VG_AES_GCM_OPEN_AES_FEATURES,
                VG_AES_GCM_STREAM_INIT_AES_FEATURES,
                VG_AES_GCM_STREAM_AAD_AES_FEATURES,
                VG_AES_GCM_STREAM_ENCRYPT_AES_FEATURES,
                VG_AES_GCM_STREAM_DECRYPT_AES_FEATURES,
                VG_AES_GCM_STREAM_FINISH_AES_FEATURES,
                VG_AES_GCM_STREAM_VERIFY_AES_FEATURES,
            ] {
                assert!(Features::of(VG_AES_GCM_SEAL_AES_FEATURES).contains(Features::of(other)));
            }
        }
    }

    /// Encryption and decryption are inverse, for every key size, 12-byte
    /// and other nonces, and texts and additional data of whole and partial
    /// blocks; a modified tag is rejected.
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
                    k.decrypt_in_place(nonce, aad, buf, &tag).unwrap();
                    assert_eq!(buf, msg);
                }
            }
        }
    }

    /// Streaming, with the additional data or the text split at every
    /// point (around block boundaries), agrees with the one-shot functions,
    /// in both directions, with one key for every message.
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
            let mut e = k.encryptor(&nonce).unwrap();
            e.update_aad(&aad[..a]).unwrap();
            e.update_aad(&aad[a..]).unwrap();
            let mut buf = msg;
            let (x, y) = buf.split_at_mut(m);
            e.update(x).unwrap();
            e.update(y).unwrap();
            assert_eq!(buf, ct);
            assert_eq!(e.finalize(), tag);

            let mut d = k.decryptor(&nonce).unwrap();
            d.update_aad(&aad[..a]).unwrap();
            d.update_aad(&aad[a..]).unwrap();
            let (x, y) = buf.split_at_mut(m);
            d.update(x).unwrap();
            d.update(y).unwrap();
            assert_eq!(buf, msg);
            assert_eq!(d.finalize(&tag), Ok(()));
        }
        // A byte at a time.
        let mut e = k.encryptor(&nonce).unwrap();
        for b in aad.chunks(1) {
            e.update_aad(b).unwrap();
        }
        let mut buf = msg;
        for b in buf.chunks_mut(1) {
            e.update(b).unwrap();
        }
        assert_eq!(buf, ct);
        assert_eq!(e.finalize(), tag);
        // Without text, or without either.
        let mut t = [0u8; 0];
        let tag = k.encrypt_in_place(&nonce, &aad[..5], &mut t).unwrap();
        let mut e = k.encryptor(&nonce).unwrap();
        e.update_aad(&aad[..5]).unwrap();
        assert_eq!(e.finalize(), tag);
        let tag = k.encrypt_in_place(&nonce, &[], &mut t).unwrap();
        let e = k.encryptor(&nonce).unwrap();
        assert_eq!(e.finalize(), tag);
        let d = k.decryptor(&nonce).unwrap();
        assert_eq!(d.finalize(&tag), Ok(()));
    }

    /// A clone continues the message independently of the original.
    #[test]
    fn stream_clone() {
        let k = AesGcm::new(&[1; 24]).unwrap();
        let nonce = [2u8; 12];
        let msg = [3u8; 20];
        let mut ct = msg;
        let tag = k.encrypt_in_place(&nonce, &[4; 8], &mut ct).unwrap();

        let mut e = k.encryptor(&nonce).unwrap();
        e.update_aad(&[4; 8]).unwrap();
        let mut other = e.clone();
        other.update(&mut [0; 1]).unwrap();
        let mut buf = msg;
        e.update(&mut buf).unwrap();
        assert_eq!((buf, e.finalize()), (ct, tag));
        assert_ne!(other.finalize(), tag);

        let mut d = k.decryptor(&nonce).unwrap();
        d.update_aad(&[4; 8]).unwrap();
        let mut other = d.clone();
        other.update(&mut [0; 1]).unwrap();
        let mut buf = ct;
        d.update(&mut buf).unwrap();
        assert_eq!(buf, msg);
        assert_eq!(d.finalize(&tag), Ok(()));
        assert_eq!(other.finalize(&tag), Err(Error::TagMismatch));
    }

    /// A tag truncated to `N` bytes: its first `N` bytes are accepted, one
    /// at a time and streaming, and any other `N` bytes (a bit flipped in
    /// each byte) are rejected, leaving the ciphertext unchanged.
    fn truncated<const N: usize>() {
        let key = [3u8; 16];
        let nonce = [4u8; 12];
        let aad = [5u8; 20];
        let msg: [u8; 37] = core::array::from_fn(|i| i as u8);
        let k = AesGcm::new(&key).unwrap();
        let mut ct = msg;
        let full = k.encrypt_in_place(&nonce, &aad, &mut ct).unwrap();
        let tag: [u8; N] = full[..N].try_into().unwrap();
        let mut buf = ct;
        k.decrypt_in_place_truncated(&nonce, &aad, &mut buf, &tag)
            .unwrap();
        assert_eq!(buf, msg);
        let stream = |tag: &[u8; N]| {
            let mut d = k.decryptor(&nonce).unwrap();
            d.update_aad(&aad).unwrap();
            let mut buf = ct;
            d.update(&mut buf).unwrap();
            assert_eq!(buf, msg);
            d.finalize_truncated(tag)
        };
        assert_eq!(stream(&tag), Ok(()));
        for i in 0..N {
            let mut bad = tag;
            bad[i] ^= 0x80;
            let mut buf = ct;
            assert_eq!(
                k.decrypt_in_place_truncated(&nonce, &aad, &mut buf, &bad),
                Err(Error::TagMismatch)
            );
            assert_eq!(buf, ct);
            assert_eq!(stream(&bad), Err(Error::TagMismatch));
        }
    }

    /// Every tag length §5.2.1.2 allows.
    #[test]
    fn truncated_tags() {
        truncated::<4>();
        truncated::<8>();
        truncated::<12>();
        truncated::<13>();
        truncated::<14>();
        truncated::<15>();
        truncated::<16>();
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
            k.decrypt_in_place(&[0; 12], &[], &mut buf, &[0; 16]),
            Err(Error::TagMismatch)
        );
        assert_eq!(buf, [0; 3]);

        assert_eq!(k.encryptor(&[]).err(), Some(Error::InvalidNonceLength));
        assert_eq!(k.decryptor(&[]).err(), Some(Error::InvalidNonceLength));
        let mut e = k.encryptor(&[0; 12]).unwrap();
        e.update(&mut buf).unwrap();
        assert_eq!(e.update_aad(&[1]), Err(Error::AadAfterText));
        let mut d = k.decryptor(&[0; 12]).unwrap();
        d.update(&mut buf).unwrap();
        assert_eq!(d.update_aad(&[1]), Err(Error::AadAfterText));
        assert_eq!(d.finalize(&[0; 16]), Err(Error::TagMismatch));

        // The length limits (§5.2.1.1), which no test can reach with real
        // buffers.
        assert_eq!(add_len(MAX_TEXT - 1, 1, MAX_TEXT), Ok(MAX_TEXT));
        assert_eq!(add_len(MAX_TEXT, 1, MAX_TEXT), Err(()));
        assert_eq!(add_len(MAX_AAD, 0, MAX_AAD), Ok(MAX_AAD));
        assert_eq!(add_len(u64::MAX, 1, MAX_AAD), Err(()));
        let mut e = k.encryptor(&[0; 12]).unwrap();
        e.stream.text_len = MAX_TEXT;
        assert_eq!(e.update(&mut buf), Err(Error::InvalidTextLength));
        e.stream.aad_len = MAX_AAD;
        e.stream.in_text = false;
        assert_eq!(e.update_aad(&[1]), Err(Error::InvalidAadLength));
        let mut d = k.decryptor(&[0; 12]).unwrap();
        d.stream.text_len = MAX_TEXT;
        assert_eq!(d.update(&mut buf), Err(Error::InvalidTextLength));
        d.stream.aad_len = MAX_AAD;
        assert_eq!(d.update_aad(&[1]), Err(Error::InvalidAadLength));
    }
}
