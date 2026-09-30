//! ML-KEM-768 (FIPS 203), the module-lattice-based key-encapsulation
//! mechanism, at security category 3.
//!
//! Key generation, encapsulation and decapsulation are the verified
//! assembly functions `vg_mlkem768_keygen`, `vg_mlkem768_encaps` and
//! `vg_mlkem768_decaps` (contracts `VG.Spec.MlKem.keyGenContract`,
//! `encapsContract` and `decapsContract`): FIPS 203's internal algorithms
//! `ML-KEM.KeyGen_internal`, `ML-KEM.Encaps_internal` and
//! `ML-KEM.Decaps_internal` (§6), which compose the verified polynomial
//! arithmetic and SHA-3. The encapsulation key check of §7.2 is
//! `vg_mlkem768_check_ek`. This module supplies their randomness and working
//! space, and destroys the intermediate values (§3.3).
//!
//! A decapsulation key is kept as the 64-byte seed `d ‖ z` it is generated
//! from (§3.3), which [`DecapsulationKey768::from_seed`] expands; the caller
//! generates the seed with an approved RBG. The expanded decapsulation key is
//! never exposed, so the decapsulation keys this module uses pass the checks
//! of §7.3 by construction. An encapsulation key from elsewhere passes the
//! check of §7.2 in [`EncapsulationKey768::from_bytes`].
//!
//! The bound on `SampleNTT`'s loop (280 iterations, as Appendix B allows) is
//! reached with probability less than 2⁻²⁶¹; the operation then fails with
//! [`Error::SampleBound`].
//!
//! On x86-64, an encapsulation key is kept expanded: with `H(ek)` and the
//! matrix `Â` that encapsulation and decapsulation sample from it, computed
//! once (by `vg_mlkem768_keygen_expanded` or `vg_mlkem768_expand_ek`,
//! contracts `VG.Spec.MlKem.keyGenExpandedContract` and `expandEkContract`),
//! so that encapsulation and decapsulation (`vg_mlkem768_encaps_expanded`
//! and `vg_mlkem768_decaps_expanded`) sample nothing: they compute the same
//! functions of FIPS 203 in about half and three quarters of the time, and
//! cannot fail. Key generation and key expansion have an instance for each
//! implementation of `vg_mlkem_sample_ntt4`, which samples four entries of
//! the matrix at once, and each operation calls the best one the CPU can run
//! ([`Backend`]).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use crate::arch::mlkem768::vg_mlkem768_check_ek;
#[cfg(target_arch = "x86_64")]
use crate::arch::mlkem768::{
    VG_MLKEM768_EXPAND_EK_AVX2_FEATURES, VG_MLKEM768_KEYGEN_EXPANDED_AVX2_FEATURES,
    vg_mlkem768_decaps_expanded, vg_mlkem768_encaps_expanded, vg_mlkem768_expand_ek,
    vg_mlkem768_expand_ek_avx2, vg_mlkem768_keygen_expanded, vg_mlkem768_keygen_expanded_avx2,
};
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::mlkem768::{vg_mlkem768_decaps, vg_mlkem768_encaps, vg_mlkem768_keygen};
#[cfg(target_arch = "x86_64")]
use crate::arch::mlkem1024::{
    VG_MLKEM1024_EXPAND_EK_AVX2_FEATURES, VG_MLKEM1024_KEYGEN_EXPANDED_AVX2_FEATURES,
};
#[cfg(target_arch = "x86_64")]
use crate::cpu::{Features, detected};

/// Why an operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// A `SampleNTT` reached the bound on its loop's iterations (FIPS 203
    /// Appendix B), which happens with probability less than 2⁻²⁶¹.
    SampleBound,
    /// The encapsulation key failed the check of FIPS 203 §7.2.
    InvalidKey,
    /// The operating system's random number generator failed.
    Randomness,
}

/// The implementations of `vg_mlkem_sample_ntt4`, which the functions that
/// sample the matrix (of ML-KEM-768 and ML-KEM-1024) follow: each has an
/// instance calling each of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The target's baseline ISA (on x86-64, `SampleNTT` on one seed at a
    /// time; elsewhere, one entry of the matrix at a time).
    Scalar,
    /// AVX2: four instances of SHAKE128 at once.
    #[cfg(target_arch = "x86_64")]
    Avx2,
}

impl Backend {
    /// The best implementation the CPU can run: [`Backend::Avx2`] if it has
    /// the features of every instance for AVX2.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select() -> Backend {
        if detected().contains(Features::all(&[
            VG_MLKEM768_KEYGEN_EXPANDED_AVX2_FEATURES,
            VG_MLKEM768_EXPAND_EK_AVX2_FEATURES,
            VG_MLKEM1024_KEYGEN_EXPANDED_AVX2_FEATURES,
            VG_MLKEM1024_EXPAND_EK_AVX2_FEATURES,
        ])) {
            Backend::Avx2
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation the CPU can run: there is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    pub(crate) fn select() -> Backend {
        Backend::Scalar
    }
}

/// The working space of the assembly functions (32 KiB).
type Scratch = [u64; 4096];

/// Overwrites `x` with zeros in a way the compiler does not remove.
pub(crate) fn zeroize<T: Copy + Default>(x: &mut [T]) {
    for v in x.iter_mut() {
        // SAFETY: `v` is a valid, aligned, unique reference.
        unsafe { core::ptr::write_volatile(v, T::default()) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// The bytes an encapsulation key is kept as: on x86-64, its expanded key
/// (the key, `H(ek)` and `Â`; see `VG.Spec.MlKem.ExpandedEk`), and elsewhere
/// the key itself.
#[cfg(target_arch = "x86_64")]
const KEPT: usize = 10432;
#[cfg(not(target_arch = "x86_64"))]
const KEPT: usize = 1184;

/// An ML-KEM-768 encapsulation key, which passed the check of FIPS 203 §7.2.
#[derive(Clone, PartialEq, Eq)]
pub struct EncapsulationKey768 {
    /// The key, and on x86-64 the rest of its expanded key (written by
    /// `vg_mlkem768_keygen_expanded` or `vg_mlkem768_expand_ek`, in a call
    /// that returned 1).
    bytes: [u8; KEPT],
}

impl core::fmt::Debug for EncapsulationKey768 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("EncapsulationKey768")
            .finish_non_exhaustive()
    }
}

impl EncapsulationKey768 {
    /// The size of an encapsulation key, in bytes.
    pub const SIZE: usize = 1184;
    /// The size of a ciphertext, in bytes.
    pub const CIPHERTEXT_SIZE: usize = 1088;
    /// The size of a shared secret key, in bytes.
    pub const SHARED_KEY_SIZE: usize = 32;

    /// The encapsulation key `bytes`, if it passes the encapsulation key
    /// check of FIPS 203 §7.2 (every integer it encodes is less than `q`);
    /// [`Error::InvalidKey`] otherwise. On x86-64, this expands the key,
    /// sampling the matrix `Â` of its `ρ`, which fails with
    /// [`Error::SampleBound`] with probability less than 2⁻²⁶¹.
    pub fn from_bytes(bytes: &[u8; 1184]) -> Result<Self, Error> {
        // SAFETY: `bytes` is valid for reads of 1184 bytes, and a Rust
        // object, so it does not overlap the stack or wrap around the end of
        // the address space.
        if unsafe { vg_mlkem768_check_ek(bytes) } != 1 {
            return Err(Error::InvalidKey);
        }
        Self::expand(bytes)
    }

    /// The key `bytes`, which passed `vg_mlkem768_check_ek`, expanded.
    #[cfg(target_arch = "x86_64")]
    fn expand(bytes: &[u8; 1184]) -> Result<Self, Error> {
        let mut key = EncapsulationKey768 { bytes: [0; KEPT] };
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `bytes`, `key.bytes` and `scratch` are valid for reads
        // (and, for the last two, writes) of their sizes; they are distinct
        // Rust objects, so they do not overlap each other or the stack, or
        // wrap around the end of the address space. `bytes` passed
        // `vg_mlkem768_check_ek`. `Backend::select` chose AVX2 only if the
        // CPU has `VG_MLKEM768_EXPAND_EK_AVX2_FEATURES`.
        let r = unsafe {
            match Backend::select() {
                Backend::Scalar => vg_mlkem768_expand_ek(bytes, &mut key.bytes, &mut scratch),
                Backend::Avx2 => vg_mlkem768_expand_ek_avx2(bytes, &mut key.bytes, &mut scratch),
            }
        };
        zeroize(&mut scratch);
        if r != 1 {
            // `SampleNTT` reaches its bound with probability less than 2^-261.
            // NO-COVERAGE-START
            return Err(Error::SampleBound);
            // NO-COVERAGE-END
        }
        Ok(key)
    }

    /// The key `bytes`, which passed `vg_mlkem768_check_ek`.
    #[cfg(not(target_arch = "x86_64"))]
    fn expand(bytes: &[u8; 1184]) -> Result<Self, Error> {
        Ok(EncapsulationKey768 { bytes: *bytes })
    }

    /// The bytes of the key.
    pub fn as_bytes(&self) -> &[u8; 1184] {
        // `KEPT` is at least 1184.
        self.bytes.first_chunk().unwrap()
    }

    /// `ML-KEM.Encaps` (FIPS 203 Algorithm 20): a shared secret key and its
    /// ciphertext, with 32 bytes of randomness from the operating system.
    pub fn encapsulate(&self) -> Result<([u8; 32], [u8; 1088]), Error> {
        let mut m = [0u8; 32];
        if getrandom::fill(&mut m).is_err() {
            // The operating system's generator does not fail in the tests.
            // NO-COVERAGE-START
            return Err(Error::Randomness);
            // NO-COVERAGE-END
        }
        let r = self.encapsulate_internal(&m);
        zeroize(&mut m);
        r
    }

    /// `ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17), with the
    /// randomness `m`: for known-answer tests only. FIPS 203 §6 allows this
    /// function only for testing; `m` must otherwise be fresh random bytes
    /// from an approved RBG, which [`encapsulate`](Self::encapsulate) draws.
    #[doc(hidden)]
    #[cfg(target_arch = "x86_64")]
    pub fn encapsulate_internal(&self, m: &[u8; 32]) -> Result<([u8; 32], [u8; 1088]), Error> {
        let mut key = [0u8; 32];
        let mut ct = [0u8; 1088];
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `self.bytes`, `m`, `key`, `ct` and `scratch` are valid for
        // reads (and, for the last three, writes) of their sizes; they are
        // distinct Rust objects, so they do not overlap each other or the
        // stack, or wrap around the end of the address space. `self.bytes`
        // was written by `vg_mlkem768_keygen_expanded` or by
        // `vg_mlkem768_expand_ek` from a key that passed
        // `vg_mlkem768_check_ek`, in a call that returned 1 (or an instance
        // of them).
        unsafe { vg_mlkem768_encaps_expanded(&self.bytes, m, &mut key, &mut ct, &mut scratch) };
        zeroize(&mut scratch);
        Ok((key, ct))
    }

    /// `ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17), with the
    /// randomness `m`: for known-answer tests only. FIPS 203 §6 allows this
    /// function only for testing; `m` must otherwise be fresh random bytes
    /// from an approved RBG, which [`encapsulate`](Self::encapsulate) draws.
    #[doc(hidden)]
    #[cfg(not(target_arch = "x86_64"))]
    pub fn encapsulate_internal(&self, m: &[u8; 32]) -> Result<([u8; 32], [u8; 1088]), Error> {
        let mut key = [0u8; 32];
        let mut ct = [0u8; 1088];
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `self.bytes`, `m`, `key`, `ct` and `scratch` are valid for
        // reads (and, for the last three, writes) of their sizes; they are
        // distinct Rust objects, so they do not overlap each other or the
        // stack, or wrap around the end of the address space. `self.bytes`
        // passed `vg_mlkem768_check_ek`.
        let r = unsafe {
            match Backend::select() {
                Backend::Scalar => {
                    vg_mlkem768_encaps(&self.bytes, m, &mut key, &mut ct, &mut scratch)
                }
            }
        };
        zeroize(&mut scratch);
        if r != 1 {
            // `SampleNTT` reaches its bound with probability less than 2^-261.
            // NO-COVERAGE-START
            zeroize(&mut key);
            zeroize(&mut ct);
            return Err(Error::SampleBound);
            // NO-COVERAGE-END
        }
        Ok((key, ct))
    }
}

/// An ML-KEM-768 decapsulation key, kept as the seed `d ‖ z` it is generated
/// from, with the keys it expands to. The seed and the expanded key are
/// destroyed when it is dropped.
pub struct DecapsulationKey768 {
    seed: [u8; 64],
    ek: EncapsulationKey768,
    dk: [u8; 2400],
}

impl core::fmt::Debug for DecapsulationKey768 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("DecapsulationKey768")
            .finish_non_exhaustive()
    }
}

impl Drop for DecapsulationKey768 {
    fn drop(&mut self) {
        zeroize(&mut self.seed);
        zeroize(&mut self.dk);
    }
}

impl DecapsulationKey768 {
    /// The size of a seed, in bytes.
    pub const SEED_SIZE: usize = 64;

    /// The key pair of the seed `d ‖ z` (`d` its first 32 bytes, `z` the
    /// last 32): `ML-KEM.KeyGen_internal(d, z)` (FIPS 203 Algorithm 16).
    /// The seed must be 64 random bytes from an approved RBG (FIPS 203
    /// §3.3, Algorithm 19), or a seed so generated before.
    pub fn from_seed(seed: &[u8; 64]) -> Result<Self, Error> {
        let mut key = DecapsulationKey768 {
            seed: *seed,
            ek: EncapsulationKey768 { bytes: [0; KEPT] },
            dk: [0; 2400],
        };
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `seed`, `key.ek.bytes`, `key.dk` and `scratch` are valid
        // for reads (and, for the last three, writes) of their sizes; they
        // are distinct Rust objects, so they do not overlap each other or
        // the stack, or wrap around the end of the address space.
        // `Backend::select` chose AVX2 only if the CPU has
        // `VG_MLKEM768_KEYGEN_EXPANDED_AVX2_FEATURES`.
        #[cfg(target_arch = "x86_64")]
        let r = unsafe {
            match Backend::select() {
                Backend::Scalar => {
                    vg_mlkem768_keygen_expanded(seed, &mut key.ek.bytes, &mut key.dk, &mut scratch)
                }
                Backend::Avx2 => vg_mlkem768_keygen_expanded_avx2(
                    seed,
                    &mut key.ek.bytes,
                    &mut key.dk,
                    &mut scratch,
                ),
            }
        };
        // SAFETY: as above.
        #[cfg(not(target_arch = "x86_64"))]
        let r = unsafe {
            match Backend::select() {
                Backend::Scalar => {
                    vg_mlkem768_keygen(seed, &mut key.ek.bytes, &mut key.dk, &mut scratch)
                }
            }
        };
        zeroize(&mut scratch);
        if r != 1 {
            // `SampleNTT` reaches its bound with probability less than 2^-261;
            // dropping `key` destroys it.
            // NO-COVERAGE-START
            return Err(Error::SampleBound);
            // NO-COVERAGE-END
        }
        Ok(key)
    }

    /// The seed `d ‖ z`.
    pub fn seed(&self) -> &[u8; 64] {
        &self.seed
    }

    /// The encapsulation key.
    pub fn encapsulation_key(&self) -> &EncapsulationKey768 {
        &self.ek
    }

    /// `ML-KEM.Decaps` (FIPS 203 Algorithm 21): the shared secret key of the
    /// ciphertext `ct`, which is the implicit rejection key `J(z ‖ ct)` if
    /// `ct` is not a ciphertext of this key (in constant time: nothing
    /// tells whether it was rejected).
    #[cfg(target_arch = "x86_64")]
    pub fn decapsulate(&self, ct: &[u8; 1088]) -> Result<[u8; 32], Error> {
        let mut key = [0u8; 32];
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `self.dk`, `self.ek.bytes`, `ct`, `key` and `scratch` are
        // valid for reads (and, for the last two, writes) of their sizes;
        // they are Rust objects, the last two distinct from the others, so
        // they do not overlap each other (but for the first three, which
        // only the function reads) or the stack, or wrap around the end of
        // the address space. `self.dk` and `self.ek.bytes` were written by
        // `vg_mlkem768_keygen_expanded` (or an instance of it) in a call that
        // returned 1.
        unsafe {
            vg_mlkem768_decaps_expanded(&self.dk, &self.ek.bytes, ct, &mut key, &mut scratch)
        };
        zeroize(&mut scratch);
        Ok(key)
    }

    /// `ML-KEM.Decaps` (FIPS 203 Algorithm 21): the shared secret key of the
    /// ciphertext `ct`, which is the implicit rejection key `J(z ‖ ct)` if
    /// `ct` is not a ciphertext of this key (in constant time: nothing
    /// tells whether it was rejected).
    #[cfg(not(target_arch = "x86_64"))]
    pub fn decapsulate(&self, ct: &[u8; 1088]) -> Result<[u8; 32], Error> {
        let mut key = [0u8; 32];
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `self.dk`, `ct`, `key` and `scratch` are valid for reads
        // (and, for the last two, writes) of their sizes; they are distinct
        // Rust objects, so they do not overlap each other or the stack, or
        // wrap around the end of the address space. `self.dk` was written by
        // `vg_mlkem768_keygen`.
        let r = unsafe {
            match Backend::select() {
                Backend::Scalar => vg_mlkem768_decaps(&self.dk, ct, &mut key, &mut scratch),
            }
        };
        zeroize(&mut scratch);
        if r != 1 {
            // `SampleNTT` reaches its bound with probability less than 2^-261.
            // NO-COVERAGE-START
            zeroize(&mut key);
            return Err(Error::SampleBound);
            // NO-COVERAGE-END
        }
        Ok(key)
    }
}

#[cfg(test)]
mod tests {
    use super::zeroize;

    #[test]
    fn zeroizes() {
        let mut x = [1u8, 2, 3];
        zeroize(&mut x);
        assert_eq!(x, [0; 3]);
    }
}
