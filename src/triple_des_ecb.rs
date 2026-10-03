//! Triple DES ECB (FIPS 46-3), in place and without padding.
//!
//! Key expansion and ECB encryption/decryption use verified primitives.
//! Each operation accepts complete eight-byte blocks, including empty input.
//! On x86-64 with AVX-512F, ECB runs 512 blocks at a time while that many
//! are left (`Backend::Avx512`), and with AVX2, 256 (`Backend::Avx2`);
//! elsewhere, and for the rest, 64 at a time.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::triple_des::{
    VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES, VG_TRIPLE_DES_ECB_DECRYPT_AVX512_FEATURES,
    VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES, VG_TRIPLE_DES_ECB_ENCRYPT_AVX512_FEATURES,
    vg_triple_des_ecb_decrypt_avx2, vg_triple_des_ecb_decrypt_avx512,
    vg_triple_des_ecb_encrypt_avx2, vg_triple_des_ecb_encrypt_avx512,
};
use crate::arch::triple_des::{
    vg_triple_des_ecb_decrypt, vg_triple_des_ecb_encrypt, vg_triple_des_expand_key,
};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The implementations of ECB encryption and decryption.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// Bitsliced, 64 blocks at a time, for the target's baseline ISA.
    Scalar,
    /// AVX2, 256 blocks at a time.
    #[cfg(target_arch = "x86_64")]
    Avx2,
    /// AVX-512F, 512 blocks at a time.
    #[cfg(target_arch = "x86_64")]
    Avx512,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select(f: Features) -> Backend {
        if f.contains(Features::all(&[
            VG_TRIPLE_DES_ECB_ENCRYPT_AVX512_FEATURES,
            VG_TRIPLE_DES_ECB_DECRYPT_AVX512_FEATURES,
        ])) {
            Backend::Avx512
        } else if f.contains(Features::all(&[
            VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES,
            VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES,
        ])) {
            Backend::Avx2
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    pub(crate) fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

/// Why a Triple DES ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16 or 24 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of eight bytes.
    IncompleteBlock,
}

/// An expanded Triple DES key for ECB encryption and decryption.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored; weak and
/// repeated component keys are accepted. No padding is added or removed.
pub struct TripleDesEcb {
    schedule: [u8; 384],
    backend: Backend,
}

impl TripleDesEcb {
    /// Expands a 16- or 24-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24) {
            return Err(Error::InvalidKeyLength);
        }
        let mut schedule = [0; 384];
        let mut scratch = [0u64; 64];
        // SAFETY: the key has a validated length; key, schedule and scratch
        // are separate valid buffers of the required sizes.
        unsafe {
            vg_triple_des_expand_key(key.as_ptr(), key.len(), &mut schedule, &mut scratch);
        }
        zeroize(&mut scratch);
        Ok(Self {
            schedule,
            backend: Backend::select(detected()),
        })
    }

    /// Encrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, true)
    }

    /// Decrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, false)
    }

    fn crypt(&self, buffer: &mut [u8], encrypt: bool) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(8) {
            return Err(Error::IncompleteBlock);
        }
        let f = match (self.backend, encrypt) {
            (Backend::Scalar, true) => vg_triple_des_ecb_encrypt,
            (Backend::Scalar, false) => vg_triple_des_ecb_decrypt,
            #[cfg(target_arch = "x86_64")]
            (Backend::Avx2, true) => vg_triple_des_ecb_encrypt_avx2,
            #[cfg(target_arch = "x86_64")]
            (Backend::Avx2, false) => vg_triple_des_ecb_decrypt_avx2,
            #[cfg(target_arch = "x86_64")]
            (Backend::Avx512, true) => vg_triple_des_ecb_encrypt_avx512,
            #[cfg(target_arch = "x86_64")]
            (Backend::Avx512, false) => vg_triple_des_ecb_decrypt_avx512,
        };
        let mut scratch = [0u64; 128];
        // SAFETY: buffer contains complete eight-byte blocks, including zero
        // blocks. The buffer, schedule and scratch are separate valid objects
        // and do not overlap the callee's stack. `Backend::select` chose `f`
        // for the CPU's features.
        unsafe {
            f(
                &self.schedule,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
                &mut scratch,
            );
        }
        zeroize(&mut scratch);
        Ok(())
    }
}

impl Drop for TripleDesEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{Backend, TripleDesEcb};
    use crate::cpu::detected;

    /// The implementation chosen for each set of features.
    #[test]
    fn select() {
        let best = TripleDesEcb::new(&[0; 24]).unwrap().backend;
        assert_eq!(best, Backend::select(detected()));
        #[cfg(target_arch = "x86_64")]
        {
            use crate::arch::triple_des::{
                VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES, VG_TRIPLE_DES_ECB_DECRYPT_AVX512_FEATURES,
                VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES, VG_TRIPLE_DES_ECB_ENCRYPT_AVX512_FEATURES,
            };
            use crate::cpu::Features;
            assert_eq!(
                Backend::select(Features::all(&[
                    VG_TRIPLE_DES_ECB_ENCRYPT_AVX512_FEATURES,
                    VG_TRIPLE_DES_ECB_DECRYPT_AVX512_FEATURES,
                    VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES,
                    VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES
                ])),
                Backend::Avx512
            );
            assert_eq!(
                Backend::select(Features::all(&[
                    VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES,
                    VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES
                ])),
                Backend::Avx2
            );
            assert_eq!(Backend::select(Features::of(&["avx"])), Backend::Scalar);
        }
    }
}
