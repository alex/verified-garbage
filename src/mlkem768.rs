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

#![cfg(any(target_arch = "x86_64", target_arch = "arm"))]

use crate::arch::mlkem768::{
    vg_mlkem768_check_ek, vg_mlkem768_decaps, vg_mlkem768_encaps, vg_mlkem768_keygen,
};

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

/// The working space of the assembly functions (32 KiB).
type Scratch = [u64; 4096];

/// Overwrites `x` with zeros in a way the compiler does not remove.
fn zeroize<T: Copy + Default>(x: &mut [T]) {
    for v in x.iter_mut() {
        // SAFETY: `v` is a valid, aligned, unique reference.
        unsafe { core::ptr::write_volatile(v, T::default()) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// An ML-KEM-768 encapsulation key, which passed the check of FIPS 203 §7.2.
#[derive(Clone, PartialEq, Eq)]
pub struct EncapsulationKey768 {
    bytes: [u8; 1184],
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
    /// [`Error::InvalidKey`] otherwise.
    pub fn from_bytes(bytes: &[u8; 1184]) -> Result<Self, Error> {
        // SAFETY: `bytes` is valid for reads of 1184 bytes, and a Rust
        // object, so it does not overlap the stack or wrap around the end of
        // the address space.
        if unsafe { vg_mlkem768_check_ek(bytes) } == 1 {
            Ok(EncapsulationKey768 { bytes: *bytes })
        } else {
            Err(Error::InvalidKey)
        }
    }

    /// The bytes of the key.
    pub fn as_bytes(&self) -> &[u8; 1184] {
        &self.bytes
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
    pub fn encapsulate_internal(&self, m: &[u8; 32]) -> Result<([u8; 32], [u8; 1088]), Error> {
        let mut key = [0u8; 32];
        let mut ct = [0u8; 1088];
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `self.bytes`, `m`, `key`, `ct` and `scratch` are valid for
        // reads (and, for the last three, writes) of their sizes; they are
        // distinct Rust objects, so they do not overlap each other or the
        // stack, or wrap around the end of the address space. `self.bytes`
        // passed `vg_mlkem768_check_ek`.
        let r = unsafe { vg_mlkem768_encaps(&self.bytes, m, &mut key, &mut ct, &mut scratch) };
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
            ek: EncapsulationKey768 { bytes: [0; 1184] },
            dk: [0; 2400],
        };
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `seed`, `key.ek.bytes`, `key.dk` and `scratch` are valid
        // for reads (and, for the last three, writes) of their sizes; they
        // are distinct Rust objects, so they do not overlap each other or
        // the stack, or wrap around the end of the address space.
        let r = unsafe { vg_mlkem768_keygen(seed, &mut key.ek.bytes, &mut key.dk, &mut scratch) };
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
    pub fn decapsulate(&self, ct: &[u8; 1088]) -> Result<[u8; 32], Error> {
        let mut key = [0u8; 32];
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `self.dk`, `ct`, `key` and `scratch` are valid for reads
        // (and, for the last two, writes) of their sizes; they are distinct
        // Rust objects, so they do not overlap each other or the stack, or
        // wrap around the end of the address space. `self.dk` was written by
        // `vg_mlkem768_keygen`.
        let r = unsafe { vg_mlkem768_decaps(&self.dk, ct, &mut key, &mut scratch) };
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
