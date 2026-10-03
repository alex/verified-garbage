//! AES-SIV (RFC 5297) with 256-, 384- and 512-bit keys (AES-128, AES-192
//! and AES-256 for each half): deterministic authenticated encryption, and
//! nonce-based when the caller passes a nonce as the last associated-data
//! component (RFC 5297 §3).
//!
//! The whole AEAD is verified assembly: `vg_aes_siv_init` (contract
//! `VG.Spec.Siv.initContract`) writes the key context (the key schedule of
//! `K1` and its CMAC subkeys, and the key schedule of `K2`),
//! `vg_aes_siv_s2v_start` and `vg_aes_siv_s2v_ad` (`s2vStartContract`,
//! `s2vAdContract`) run S2V over the associated data, and
//! `vg_aes_siv_seal` and `vg_aes_siv_open` (`sealContract`, `openContract`)
//! finish it with the plaintext and encrypt, or decrypt and finish it and
//! compare, in constant time. `open` overwrites the data with zeros when the
//! synthetic IV is wrong. This module checks the number of components
//! (RFC 5297 §2.6 allows at most 126 besides the plaintext), which the
//! assembly does not count, and holds the key context.
//!
//! The functions are emitted once for each implementation of AES they call
//! (`vg_aes_expand_key` and `vg_aes_ctr32`, through the CMAC functions made
//! with them, and directly for CTR), which have the same contracts: on
//! x86-64, CPUs with AES-NI and SSSE3 run the `_aesni` instances, and CPUs
//! with VAES and AVX2 too the `_vaes` ones (`crate::aes::Backend`). Only
//! x86-64 has an implementation so far.

#![cfg(target_arch = "x86_64")]

use crate::aes::Backend;
use crate::arch::aes_siv::{
    VG_AES_SIV_INIT_AESNI_FEATURES, VG_AES_SIV_INIT_VAES_FEATURES, VG_AES_SIV_OPEN_AESNI_FEATURES,
    VG_AES_SIV_OPEN_VAES_FEATURES, VG_AES_SIV_S2V_AD_AESNI_FEATURES,
    VG_AES_SIV_S2V_AD_VAES_FEATURES, VG_AES_SIV_S2V_START_AESNI_FEATURES,
    VG_AES_SIV_S2V_START_VAES_FEATURES, VG_AES_SIV_SEAL_AESNI_FEATURES,
    VG_AES_SIV_SEAL_VAES_FEATURES, vg_aes_siv_init, vg_aes_siv_init_aesni, vg_aes_siv_init_vaes,
    vg_aes_siv_open, vg_aes_siv_open_aesni, vg_aes_siv_open_vaes, vg_aes_siv_s2v_ad,
    vg_aes_siv_s2v_ad_aesni, vg_aes_siv_s2v_ad_vaes, vg_aes_siv_s2v_start,
    vg_aes_siv_s2v_start_aesni, vg_aes_siv_s2v_start_vaes, vg_aes_siv_seal, vg_aes_siv_seal_aesni,
    vg_aes_siv_seal_vaes,
};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// A 16-byte block.
type Block = [u8; 16];

/// The working space of the functions, in 64-bit words.
const WORK: usize = 320;

/// The instance of a function for `backend`.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $vaes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            Backend::AesNi => $aesni,
            Backend::Vaes => $vaes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// the AES-SIV functions for it.
fn select(f: Features) -> Backend {
    const VAES: Features = Features::all(&[
        VG_AES_SIV_INIT_VAES_FEATURES,
        VG_AES_SIV_S2V_START_VAES_FEATURES,
        VG_AES_SIV_S2V_AD_VAES_FEATURES,
        VG_AES_SIV_SEAL_VAES_FEATURES,
        VG_AES_SIV_OPEN_VAES_FEATURES,
    ]);
    const AESNI: Features = Features::all(&[
        VG_AES_SIV_INIT_AESNI_FEATURES,
        VG_AES_SIV_S2V_START_AESNI_FEATURES,
        VG_AES_SIV_S2V_AD_AESNI_FEATURES,
        VG_AES_SIV_SEAL_AESNI_FEATURES,
        VG_AES_SIV_OPEN_AESNI_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
}

/// Why an AES-SIV operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The key is not 32, 48 or 64 bytes long.
    InvalidKeyLength,
    /// More than [`AesSiv::MAX_COMPONENTS`] associated-data components.
    TooManyComponents,
    /// The synthetic IV does not match: the ciphertext or the associated
    /// data is not what was authenticated under this key.
    TagMismatch,
}

/// An AES-SIV key: its key context. [`encrypt_in_place`](Self::encrypt_in_place)
/// is `SIV-ENCRYPT` and [`decrypt_in_place`](Self::decrypt_in_place)
/// `SIV-DECRYPT` (RFC 5297 §2.6, §2.7), with the synthetic IV `V` apart from
/// the data: the RFC's output is `V` followed by the ciphertext.
#[derive(Clone)]
pub struct AesSiv {
    /// The key context `vg_aes_siv_init` writes (`VG.Spec.Siv.KeyRepr`).
    ctx: [u64; 64],
    /// The number of rounds of AES for each half of the key.
    rounds: usize,
    /// The implementation of AES the functions called call.
    backend: Backend,
}

impl Drop for AesSiv {
    /// Wipes the key context.
    fn drop(&mut self) {
        zeroize(&mut self.ctx);
    }
}

impl AesSiv {
    /// The size of the synthetic IV, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// The most associated-data components a message may have (RFC 5297
    /// §2.6: S2V takes at most 127 strings, the last the plaintext).
    pub const MAX_COMPONENTS: usize = 126;

    /// Prepares `key`, which must be 32, 48 or 64 bytes long: `K1`, for
    /// S2V, then `K2`, for CTR, each 16, 24 or 32 bytes.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 32 | 48 | 64) {
            return Err(Error::InvalidKeyLength);
        }
        let mut k = AesSiv {
            ctx: [0; 64],
            rounds: key.len() / 8 + 6,
            backend: select(detected()),
        };
        let init = instance!(
            k.backend,
            vg_aes_siv_init,
            vg_aes_siv_init_aesni,
            vg_aes_siv_init_vaes
        );
        let mut scratch = MaybeUninit::<[u64; WORK]>::uninit();
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 32,
        // 48 or 64; `k.ctx` and `scratch` are valid for reads and writes of
        // 512 and 2560 bytes. They are distinct objects, so no two overlap,
        // nor do they overlap the return addresses on the stack or the stack
        // below them, and none wraps around the end of the address space.
        // The CPU has the features of the implementation selected. `scratch`
        // is uninitialized: it is only working space, and the contract's
        // result does not depend on what it holds.
        unsafe { init(key.as_ptr(), key.len(), &mut k.ctx, scratch.as_mut_ptr()) };
        Ok(k)
    }

    /// S2V of the associated data `ads` (RFC 5297 §2.4): the state `D` after
    /// its components, which `seal` and `open` finish with the plaintext.
    fn s2v(&self, ads: &[&[u8]], work: &mut MaybeUninit<[u64; WORK]>) -> Result<Block, Error> {
        if ads.len() > Self::MAX_COMPONENTS {
            return Err(Error::TooManyComponents);
        }
        let start = instance!(
            self.backend,
            vg_aes_siv_s2v_start,
            vg_aes_siv_s2v_start_aesni,
            vg_aes_siv_s2v_start_vaes
        );
        let ad = instance!(
            self.backend,
            vg_aes_siv_s2v_ad,
            vg_aes_siv_s2v_ad_aesni,
            vg_aes_siv_s2v_ad_vaes
        );
        let mut d = [0u8; 16];
        // SAFETY: `self.ctx` is the key context `vg_aes_siv_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds (every implementation writes
        // the same one), valid for reads of 512 bytes; `d` and `work` (a
        // borrow of the caller's working space, whose contents the result
        // does not depend on) are valid for reads and writes of 16 and 2560
        // bytes. They are distinct objects, so no two overlap, nor do they
        // overlap the return addresses on the stack or the stack below them,
        // and none wraps around the end of the address space. The CPU has
        // the features of the implementation selected.
        unsafe { start(&self.ctx, self.rounds, &mut d, work.as_mut_ptr()) };
        for s in ads {
            // SAFETY: as for `start`, with the component `s` valid for reads
            // of `s.len()` bytes, a borrow distinct from `d` and `work`.
            unsafe {
                ad(
                    &self.ctx,
                    self.rounds,
                    &mut d,
                    s.as_ptr(),
                    s.len(),
                    work.as_mut_ptr(),
                )
            };
        }
        Ok(d)
    }

    /// `SIV-ENCRYPT` (RFC 5297 §2.6): encrypts `data` in place, and returns
    /// the synthetic IV `V`, which authenticates the plaintext and the
    /// associated-data components `ads` (at most
    /// [`MAX_COMPONENTS`](Self::MAX_COMPONENTS) of them, in order). The same
    /// key, components and plaintext always give the same output: a
    /// protocol that must hide repeated messages passes a nonce as the last
    /// component.
    pub fn encrypt_in_place(&self, ads: &[&[u8]], data: &mut [u8]) -> Result<Block, Error> {
        let mut work = MaybeUninit::<[u64; WORK]>::uninit();
        let d = self.s2v(ads, &mut work)?;
        let seal = instance!(
            self.backend,
            vg_aes_siv_seal,
            vg_aes_siv_seal_aesni,
            vg_aes_siv_seal_vaes
        );
        // SAFETY: as in `s2v`, with the S2V state `d` (a local) valid for
        // reads of 16 bytes and `data` for reads and writes of `data.len()`
        // bytes, a unique borrow distinct from the others. `work` is working
        // space but for the synthetic IV written to its first 16 bytes.
        unsafe {
            seal(
                &self.ctx,
                self.rounds,
                &d,
                data.as_mut_ptr(),
                data.len(),
                work.as_mut_ptr(),
            )
        };
        // SAFETY: `seal` wrote the synthetic IV to the first 16 bytes of
        // `work`.
        Ok(unsafe { first_block(&work) })
    }

    /// `SIV-DECRYPT` (RFC 5297 §2.7): decrypts `data` in place with the
    /// synthetic IV `tag`, and checks that `tag` authenticates the plaintext
    /// and the associated-data components `ads`. If it does not, returns an
    /// error and overwrites `data` with zeros.
    pub fn decrypt_in_place(
        &self,
        ads: &[&[u8]],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        let mut work = MaybeUninit::<[u64; WORK]>::uninit();
        let d = self.s2v(ads, &mut work)?;
        let open = instance!(
            self.backend,
            vg_aes_siv_open,
            vg_aes_siv_open_aesni,
            vg_aes_siv_open_vaes
        );
        let w = work.as_mut_ptr().cast::<u64>();
        // SAFETY: `work` is valid for writes of 320 words.
        unsafe {
            w.write(u64::from_le_bytes(tag[..8].try_into().unwrap()));
            w.add(1)
                .write(u64::from_le_bytes(tag[8..].try_into().unwrap()));
        }
        // SAFETY: as in `encrypt_in_place`, with the received synthetic IV
        // in the first 16 bytes of `work`.
        let ok = unsafe {
            open(
                &self.ctx,
                self.rounds,
                &d,
                data.as_mut_ptr(),
                data.len(),
                work.as_mut_ptr(),
            )
        };
        // `open`'s contract leaves the plaintext in `data` if it returns 1,
        // and zeros otherwise.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

/// The first 16 bytes of `work`, where `seal` writes the synthetic IV.
///
/// # Safety
///
/// They must have been written.
unsafe fn first_block(work: &MaybeUninit<[u64; WORK]>) -> Block {
    let w = work.as_ptr().cast::<u64>();
    let mut b = [0u8; 16];
    // SAFETY: the first two words are initialized (the caller's guarantee).
    unsafe {
        b[..8].copy_from_slice(&w.read().to_le_bytes());
        b[8..].copy_from_slice(&w.add(1).read().to_le_bytes());
    }
    b
}

#[cfg(test)]
mod tests {
    use super::{AesSiv, Error};

    #[test]
    fn key_lengths() {
        let key = [0u8; 80];
        for n in [0, 16, 24, 31, 33, 47, 63, 65, 80] {
            assert_eq!(AesSiv::new(&key[..n]).err(), Some(Error::InvalidKeyLength));
        }
    }

    #[test]
    fn too_many_components() {
        let k = AesSiv::new(&[0; 32]).unwrap();
        let ads = [&[][..]; AesSiv::MAX_COMPONENTS + 1];
        let mut data = [1u8; 5];
        assert_eq!(
            k.encrypt_in_place(&ads, &mut data),
            Err(Error::TooManyComponents)
        );
        assert_eq!(
            k.decrypt_in_place(&ads, &mut data, &[0; 16]),
            Err(Error::TooManyComponents)
        );
        // Nothing was touched.
        assert_eq!(data, [1; 5]);
        // The most components allowed round-trip.
        let ads = &ads[..AesSiv::MAX_COMPONENTS];
        let tag = k.encrypt_in_place(ads, &mut data).unwrap();
        k.decrypt_in_place(ads, &mut data, &tag).unwrap();
        assert_eq!(data, [1; 5]);
    }
}
