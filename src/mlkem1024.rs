//! ML-KEM-1024 (FIPS 203), the module-lattice-based key-encapsulation
//! mechanism, at security category 5.
//!
//! Key generation, encapsulation and decapsulation are the verified
//! assembly functions `vg_mlkem1024_keygen`, `vg_mlkem1024_encaps` and
//! `vg_mlkem1024_decaps` (contracts `VG.Spec.MlKem1024.keyGenContract`,
//! `encapsContract` and `decapsContract`): FIPS 203's internal algorithms
//! `ML-KEM.KeyGen_internal`, `ML-KEM.Encaps_internal` and
//! `ML-KEM.Decaps_internal` (§6), which compose the verified polynomial
//! arithmetic and SHA-3. The encapsulation key check of §7.2 is
//! `vg_mlkem1024_check_ek`. This module supplies their randomness and
//! working space, and destroys the intermediate values (§3.3).
//!
//! A decapsulation key is kept as the 64-byte seed `d ‖ z` it is generated
//! from (§3.3), which [`DecapsulationKey1024::from_seed`] expands; the caller
//! generates the seed with an approved RBG. The expanded decapsulation key is
//! never exposed, so the decapsulation keys this module uses pass the checks
//! of §7.3 by construction. An encapsulation key from elsewhere passes the
//! check of §7.2 in [`EncapsulationKey1024::from_bytes`].
//!
//! The bound on `SampleNTT`'s loop (280 iterations, as Appendix B allows) is
//! reached with probability less than 2⁻²⁶¹; the operation then fails with
//! [`Error::SampleBound`].
//!
//! On x86-64, as ML-KEM-768's, an encapsulation key also keeps its
//! *expanded* key: the key, `H(ek)` and the matrix `Â` that encapsulation
//! samples from its `ρ` (contracts `VG.Spec.MlKem1024.keyGenExpandedContract`
//! and `expandEkContract`), so that encapsulating to it again samples and
//! hashes nothing but the message (`vg_mlkem1024_encaps_expanded`). A key from
//! [`EncapsulationKey1024::from_bytes`] is expanded on its second
//! encapsulation, so that a key used once costs no more than before; a
//! decapsulation key's is written by key generation
//! (`vg_mlkem1024_keygen_expanded`), and decapsulation
//! (`vg_mlkem1024_decaps_expanded`) uses it rather than sampling `Â`.
//!
//! On x86-64, the functions that sample `Â` have an instance for each
//! implementation of `vg_mlkem_sample_ntt4`, which samples four entries of
//! the matrix at once, and each operation calls the best one the CPU can
//! run (as ML-KEM-768's).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::mlkem1024::{vg_mlkem1024_check_ek, vg_mlkem1024_encaps};
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::mlkem1024::{vg_mlkem1024_decaps, vg_mlkem1024_keygen};
#[cfg(target_arch = "x86_64")]
use crate::arch::mlkem1024::{
    vg_mlkem1024_decaps_expanded, vg_mlkem1024_encaps_avx2, vg_mlkem1024_encaps_expanded,
    vg_mlkem1024_expand_ek, vg_mlkem1024_expand_ek_avx2, vg_mlkem1024_keygen_expanded,
    vg_mlkem1024_keygen_expanded_avx2,
};
pub use crate::mlkem768::Error;
#[cfg(target_arch = "x86_64")]
use crate::mlkem768::Expanded;
use crate::mlkem768::{Backend, zeroize};

/// The working space of the assembly functions (48 KiB).
type Scratch = [u64; 6144];

/// An ML-KEM-1024 encapsulation key, which passed the check of FIPS 203 §7.2.
#[derive(Clone)]
pub struct EncapsulationKey1024 {
    bytes: [u8; 1568],
    /// On x86-64, its expanded key (see `Expanded`): written by
    /// `vg_mlkem1024_keygen_expanded` with `bytes`, or by
    /// `vg_mlkem1024_expand_ek` from `bytes` (or an instance of them), in a
    /// call that returned 1.
    #[cfg(target_arch = "x86_64")]
    expanded: Expanded<17984>,
}

impl PartialEq for EncapsulationKey1024 {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl Eq for EncapsulationKey1024 {}

impl core::fmt::Debug for EncapsulationKey1024 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("EncapsulationKey1024")
            .finish_non_exhaustive()
    }
}

impl EncapsulationKey1024 {
    /// The size of an encapsulation key, in bytes.
    pub const SIZE: usize = 1568;
    /// The size of a ciphertext, in bytes.
    pub const CIPHERTEXT_SIZE: usize = 1568;
    /// The size of a shared secret key, in bytes.
    pub const SHARED_KEY_SIZE: usize = 32;

    /// The encapsulation key `bytes`, if it passes the encapsulation key
    /// check of FIPS 203 §7.2 (every integer it encodes is less than `q`);
    /// [`Error::InvalidKey`] otherwise.
    // Inlined, so that the key (with its expanded key's buffer) is built
    // where the caller keeps it rather than copied there.
    #[inline]
    pub fn from_bytes(bytes: &[u8; 1568]) -> Result<Self, Error> {
        // SAFETY: `bytes` is valid for reads of 1568 bytes, and a Rust
        // object, so it does not overlap the stack or wrap around the end of
        // the address space.
        if unsafe { vg_mlkem1024_check_ek(bytes) } == 1 {
            Ok(EncapsulationKey1024 {
                bytes: *bytes,
                #[cfg(target_arch = "x86_64")]
                expanded: Expanded::new(),
            })
        } else {
            Err(Error::InvalidKey)
        }
    }

    /// The bytes of the key.
    pub fn as_bytes(&self) -> &[u8; 1568] {
        &self.bytes
    }

    /// `ML-KEM.Encaps` (FIPS 203 Algorithm 20): a shared secret key and its
    /// ciphertext, with 32 bytes of randomness from the operating system.
    pub fn encapsulate(&self) -> Result<([u8; 32], [u8; 1568]), Error> {
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

    /// The expanded key, from `vg_mlkem1024_expand_ek` (see `Expanded`).
    #[cfg(target_arch = "x86_64")]
    fn expanded(&self) -> Option<&[u8; 17984]> {
        self.expanded.get(|ekx| {
            let mut scratch: Scratch = [0; 6144];
            // SAFETY: `self.bytes`, `ekx` and `scratch` are valid for reads
            // (and, for the last two, writes) of their sizes; they are
            // distinct Rust objects, so they do not overlap each other or the
            // stack, or wrap around the end of the address space.
            // `self.bytes` passed `vg_mlkem1024_check_ek`. `Backend::select`
            // chose AVX2 only if the CPU has
            // `VG_MLKEM1024_EXPAND_EK_AVX2_FEATURES`.
            let r = unsafe {
                match Backend::select() {
                    Backend::Scalar => vg_mlkem1024_expand_ek(&self.bytes, ekx, &mut scratch),
                    Backend::Avx2 => vg_mlkem1024_expand_ek_avx2(&self.bytes, ekx, &mut scratch),
                }
            };
            zeroize(&mut scratch);
            r == 1
        })
    }

    /// `ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17), with the
    /// randomness `m`: for known-answer tests only. FIPS 203 §6 allows this
    /// function only for testing; `m` must otherwise be fresh random bytes
    /// from an approved RBG, which [`encapsulate`](Self::encapsulate) draws.
    #[doc(hidden)]
    pub fn encapsulate_internal(&self, m: &[u8; 32]) -> Result<([u8; 32], [u8; 1568]), Error> {
        let mut key = [0u8; 32];
        let mut ct = [0u8; 1568];
        let mut scratch: Scratch = [0; 6144];
        #[cfg(target_arch = "x86_64")]
        if let Some(ekx) = self.expanded() {
            // SAFETY: `ekx`, `m`, `key`, `ct` and `scratch` are valid for
            // reads (and, for the last three, writes) of their sizes; they
            // are distinct Rust objects, so they do not overlap each other or
            // the stack, or wrap around the end of the address space. `ekx`
            // was written by `vg_mlkem1024_keygen_expanded` or by
            // `vg_mlkem1024_expand_ek` from a key that passed
            // `vg_mlkem1024_check_ek` (or an instance of them), in a call
            // that returned 1.
            unsafe { vg_mlkem1024_encaps_expanded(ekx, m, &mut key, &mut ct, &mut scratch) };
            zeroize(&mut scratch);
            return Ok((key, ct));
        }
        // SAFETY: `self.bytes`, `m`, `key`, `ct` and `scratch` are valid for
        // reads (and, for the last three, writes) of their sizes; they are
        // distinct Rust objects, so they do not overlap each other or the
        // stack, or wrap around the end of the address space. `self.bytes`
        // passed `vg_mlkem1024_check_ek`. `Backend::select` chose AVX2 only
        // if the CPU has `VG_MLKEM1024_ENCAPS_AVX2_FEATURES`.
        let r = unsafe {
            match Backend::select() {
                Backend::Scalar => {
                    vg_mlkem1024_encaps(&self.bytes, m, &mut key, &mut ct, &mut scratch)
                }
                #[cfg(target_arch = "x86_64")]
                Backend::Avx2 => {
                    vg_mlkem1024_encaps_avx2(&self.bytes, m, &mut key, &mut ct, &mut scratch)
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

/// An ML-KEM-1024 decapsulation key, kept as the seed `d ‖ z` it is
/// generated from, with the keys it expands to. The seed and the expanded
/// key are destroyed when it is dropped.
pub struct DecapsulationKey1024 {
    seed: [u8; 64],
    ek: EncapsulationKey1024,
    dk: [u8; 3168],
}

impl core::fmt::Debug for DecapsulationKey1024 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("DecapsulationKey1024")
            .finish_non_exhaustive()
    }
}

impl Drop for DecapsulationKey1024 {
    fn drop(&mut self) {
        zeroize(&mut self.seed);
        zeroize(&mut self.dk);
    }
}

impl DecapsulationKey1024 {
    /// The size of a seed, in bytes.
    pub const SEED_SIZE: usize = 64;

    /// The key pair of the seed `d ‖ z` (`d` its first 32 bytes, `z` the
    /// last 32): `ML-KEM.KeyGen_internal(d, z)` (FIPS 203 Algorithm 16).
    /// The seed must be 64 random bytes from an approved RBG (FIPS 203
    /// §3.3, Algorithm 19), or a seed so generated before.
    pub fn from_seed(seed: &[u8; 64]) -> Result<Self, Error> {
        let mut key = DecapsulationKey1024 {
            seed: *seed,
            ek: EncapsulationKey1024 {
                bytes: [0; 1568],
                #[cfg(target_arch = "x86_64")]
                expanded: Expanded::new(),
            },
            dk: [0; 3168],
        };
        let mut scratch: Scratch = [0; 6144];
        // SAFETY: `seed`, the expanded key's buffer, `key.dk` and `scratch`
        // are valid for reads (and, for the last three, writes) of their
        // sizes; they are distinct Rust objects, so they do not overlap each
        // other or the stack, or wrap around the end of the address space.
        // `Backend::select` chose AVX2 only if the CPU has
        // `VG_MLKEM1024_KEYGEN_EXPANDED_AVX2_FEATURES`.
        #[cfg(target_arch = "x86_64")]
        let r = {
            let ekx = key.ek.expanded.buffer();
            let r = unsafe {
                match Backend::select() {
                    Backend::Scalar => {
                        vg_mlkem1024_keygen_expanded(seed, ekx, &mut key.dk, &mut scratch)
                    }
                    Backend::Avx2 => {
                        vg_mlkem1024_keygen_expanded_avx2(seed, ekx, &mut key.dk, &mut scratch)
                    }
                }
            };
            // The expanded key starts with the key.
            key.ek.bytes.copy_from_slice(&ekx[..1568]);
            r
        };
        // SAFETY: `seed`, `key.ek.bytes`, `key.dk` and `scratch` are valid
        // for reads (and, for the last three, writes) of their sizes; they
        // are distinct Rust objects, so they do not overlap each other or
        // the stack, or wrap around the end of the address space.
        #[cfg(not(target_arch = "x86_64"))]
        let r = unsafe {
            match Backend::select() {
                Backend::Scalar => {
                    vg_mlkem1024_keygen(seed, &mut key.ek.bytes, &mut key.dk, &mut scratch)
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
        #[cfg(target_arch = "x86_64")]
        key.ek.expanded.set_ready();
        Ok(key)
    }

    /// The seed `d ‖ z`.
    pub fn seed(&self) -> &[u8; 64] {
        &self.seed
    }

    /// The encapsulation key.
    pub fn encapsulation_key(&self) -> &EncapsulationKey1024 {
        &self.ek
    }

    /// `ML-KEM.Decaps` (FIPS 203 Algorithm 21): the shared secret key of the
    /// ciphertext `ct`, which is the implicit rejection key `J(z ‖ ct)` if
    /// `ct` is not a ciphertext of this key (in constant time: nothing
    /// tells whether it was rejected).
    #[cfg(target_arch = "x86_64")]
    pub fn decapsulate(&self, ct: &[u8; 1568]) -> Result<[u8; 32], Error> {
        let mut key = [0u8; 32];
        let mut scratch: Scratch = [0; 6144];
        // Key generation wrote the expanded key.
        let ekx = self.ek.expanded.ready().unwrap();
        // SAFETY: `self.dk`, `ekx`, `ct`, `key` and `scratch` are valid for
        // reads (and, for the last two, writes) of their sizes; they are
        // distinct Rust objects, so they do not overlap each other or the
        // stack, or wrap around the end of the address space. `self.dk` and
        // `ekx` were written by `vg_mlkem1024_keygen_expanded` (or an
        // instance of it) in a call that returned 1.
        unsafe { vg_mlkem1024_decaps_expanded(&self.dk, ekx, ct, &mut key, &mut scratch) };
        zeroize(&mut scratch);
        Ok(key)
    }

    /// `ML-KEM.Decaps` (FIPS 203 Algorithm 21): the shared secret key of the
    /// ciphertext `ct`, which is the implicit rejection key `J(z ‖ ct)` if
    /// `ct` is not a ciphertext of this key (in constant time: nothing
    /// tells whether it was rejected).
    #[cfg(not(target_arch = "x86_64"))]
    pub fn decapsulate(&self, ct: &[u8; 1568]) -> Result<[u8; 32], Error> {
        let mut key = [0u8; 32];
        let mut scratch: Scratch = [0; 6144];
        // SAFETY: `self.dk`, `ct`, `key` and `scratch` are valid for reads
        // (and, for the last two, writes) of their sizes; they are distinct
        // Rust objects, so they do not overlap each other or the stack, or
        // wrap around the end of the address space. `self.dk` was written by
        // `vg_mlkem1024_keygen`.
        let r = unsafe {
            match Backend::select() {
                Backend::Scalar => vg_mlkem1024_decaps(&self.dk, ct, &mut key, &mut scratch),
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
