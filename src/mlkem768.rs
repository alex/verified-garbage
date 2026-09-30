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
//! On x86-64, an encapsulation key also keeps its *expanded* key: the key,
//! `H(ek)` and the matrix `Â` that encapsulation samples from its `ρ`
//! (contracts `VG.Spec.MlKem.keyGenExpandedContract` and
//! `expandEkContract`), so that encapsulating to it again samples and hashes
//! nothing but the message (`vg_mlkem768_encaps_expanded`), in about half
//! the time. A key from [`EncapsulationKey768::from_bytes`] is expanded on
//! its second encapsulation, so that a key used once costs no more than
//! before; a decapsulation key's is written by key generation
//! (`vg_mlkem768_keygen_expanded`), and decapsulation
//! (`vg_mlkem768_decaps_expanded`) uses it rather than sampling `Â`.
//!
//! On x86-64, the functions that sample `Â` have an instance for each
//! implementation of `vg_mlkem_sample_ntt4`, which samples four entries of
//! the matrix at once, and each operation calls the best one the CPU can
//! run ([`Backend`]).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

#[cfg(target_arch = "x86_64")]
use core::cell::UnsafeCell;
#[cfg(target_arch = "x86_64")]
use core::mem::MaybeUninit;
#[cfg(target_arch = "x86_64")]
use core::sync::atomic::{AtomicU8, Ordering};

#[cfg(target_arch = "x86_64")]
use crate::arch::mlkem768::{
    VG_MLKEM768_ENCAPS_AVX2_FEATURES, VG_MLKEM768_EXPAND_EK_AVX2_FEATURES,
    VG_MLKEM768_KEYGEN_EXPANDED_AVX2_FEATURES, vg_mlkem768_decaps_expanded,
    vg_mlkem768_encaps_avx2, vg_mlkem768_encaps_expanded, vg_mlkem768_expand_ek,
    vg_mlkem768_expand_ek_avx2, vg_mlkem768_keygen_expanded, vg_mlkem768_keygen_expanded_avx2,
};
use crate::arch::mlkem768::{vg_mlkem768_check_ek, vg_mlkem768_encaps};
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::mlkem768::{vg_mlkem768_decaps, vg_mlkem768_keygen};
#[cfg(target_arch = "x86_64")]
use crate::arch::mlkem1024::{
    VG_MLKEM1024_DECAPS_AVX2_FEATURES, VG_MLKEM1024_ENCAPS_AVX2_FEATURES,
    VG_MLKEM1024_KEYGEN_AVX2_FEATURES,
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
            VG_MLKEM768_ENCAPS_AVX2_FEATURES,
            VG_MLKEM768_EXPAND_EK_AVX2_FEATURES,
            VG_MLKEM1024_KEYGEN_AVX2_FEATURES,
            VG_MLKEM1024_ENCAPS_AVX2_FEATURES,
            VG_MLKEM1024_DECAPS_AVX2_FEATURES,
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

/// An encapsulation key's expanded key (`N` bytes), which it computes on its
/// second encapsulation: the first uses the key alone, so a key used once
/// costs no more than without it.
///
/// `state` says what `ekx` holds: nothing yet ([`Expanded::UNUSED`], or
/// [`Expanded::USED`] after one encapsulation), being written by the one
/// thread that moved it from `USED` ([`Expanded::BUSY`]), the expanded key
/// ([`Expanded::READY`]), or nothing ever ([`Expanded::FAILED`], if the
/// expansion reached `SampleNTT`'s bound). Only the thread that moved the
/// state to `BUSY` writes `ekx`, and nothing reads it before the state is
/// `READY`, which it never leaves; any other thread encapsulates without it
/// meanwhile. `ekx` is initialized when it is written, so that a key that
/// is never expanded costs no more than without it.
#[cfg(target_arch = "x86_64")]
pub(crate) struct Expanded<const N: usize> {
    state: AtomicU8,
    ekx: UnsafeCell<MaybeUninit<[u8; N]>>,
}

// SAFETY: `ekx` is written only by the thread that moved `state` from
// `USED` to `BUSY`, and read only after `state` is `READY` (with acquire and
// release orderings), after which it is never written.
#[cfg(target_arch = "x86_64")]
unsafe impl<const N: usize> Sync for Expanded<N> {}

#[cfg(target_arch = "x86_64")]
impl<const N: usize> Expanded<N> {
    const UNUSED: u8 = 0;
    const USED: u8 = 1;
    const BUSY: u8 = 2;
    const READY: u8 = 3;
    const FAILED: u8 = 4;

    /// Not expanded yet.
    pub(crate) fn new() -> Self {
        Expanded {
            state: AtomicU8::new(Self::UNUSED),
            ekx: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// The buffer, zeroed, for key generation to write the expanded key
    /// into (then [`set_ready`](Self::set_ready)).
    pub(crate) fn buffer(&mut self) -> &mut [u8; N] {
        self.ekx.get_mut().write([0; N])
    }

    /// Marks the buffer as holding the expanded key.
    pub(crate) fn set_ready(&mut self) {
        *self.state.get_mut() = Self::READY;
    }

    /// The expanded key, if there is one.
    pub(crate) fn ready(&self) -> Option<&[u8; N]> {
        // SAFETY: the state is `READY`, so `ekx` is initialized, and nothing
        // writes it any more.
        (self.state.load(Ordering::Acquire) == Self::READY)
            .then(|| unsafe { (*self.ekx.get()).assume_init_ref() })
    }

    /// The expanded key for an encapsulation: none on the key's first one,
    /// written by `expand` (which returns whether it did) on its second, and
    /// the same afterwards; none while another thread writes it.
    pub(crate) fn get(&self, expand: impl FnOnce(&mut [u8; N]) -> bool) -> Option<&[u8; N]> {
        match self.state.load(Ordering::Acquire) {
            Self::UNUSED => {
                let _ = self.state.compare_exchange(
                    Self::UNUSED,
                    Self::USED,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                );
                None
            }
            Self::USED
                if self
                    .state
                    .compare_exchange(Self::USED, Self::BUSY, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok() =>
            {
                // SAFETY: this thread moved the state to `BUSY`, so no other
                // thread writes `ekx` or reads it until the state is `READY`.
                let ok = expand(unsafe { (*self.ekx.get()).write([0; N]) });
                let state = if ok { Self::READY } else { Self::FAILED };
                self.state.store(state, Ordering::Release);
                self.ready()
            }
            _ => self.ready(),
        }
    }
}

#[cfg(target_arch = "x86_64")]
impl<const N: usize> Clone for Expanded<N> {
    fn clone(&self) -> Self {
        let mut e = Expanded::new();
        if let Some(ekx) = self.ready() {
            e.ekx.get_mut().write(*ekx);
            e.set_ready();
        }
        e
    }
}

/// An ML-KEM-768 encapsulation key, which passed the check of FIPS 203 §7.2.
#[derive(Clone)]
pub struct EncapsulationKey768 {
    bytes: [u8; 1184],
    /// On x86-64, its expanded key (see [`Expanded`]): written by
    /// `vg_mlkem768_keygen_expanded` with `bytes`, or by
    /// `vg_mlkem768_expand_ek` from `bytes` (or an instance of them), in a
    /// call that returned 1.
    #[cfg(target_arch = "x86_64")]
    expanded: Expanded<10432>,
}

impl PartialEq for EncapsulationKey768 {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl Eq for EncapsulationKey768 {}

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
            Ok(EncapsulationKey768 {
                bytes: *bytes,
                #[cfg(target_arch = "x86_64")]
                expanded: Expanded::new(),
            })
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

    /// The expanded key, from `vg_mlkem768_expand_ek` (see [`Expanded`]).
    #[cfg(target_arch = "x86_64")]
    fn expanded(&self) -> Option<&[u8; 10432]> {
        self.expanded.get(|ekx| {
            let mut scratch: Scratch = [0; 4096];
            // SAFETY: `self.bytes`, `ekx` and `scratch` are valid for reads
            // (and, for the last two, writes) of their sizes; they are
            // distinct Rust objects, so they do not overlap each other or the
            // stack, or wrap around the end of the address space.
            // `self.bytes` passed `vg_mlkem768_check_ek`. `Backend::select`
            // chose AVX2 only if the CPU has
            // `VG_MLKEM768_EXPAND_EK_AVX2_FEATURES`.
            let r = unsafe {
                match Backend::select() {
                    Backend::Scalar => vg_mlkem768_expand_ek(&self.bytes, ekx, &mut scratch),
                    Backend::Avx2 => vg_mlkem768_expand_ek_avx2(&self.bytes, ekx, &mut scratch),
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
    pub fn encapsulate_internal(&self, m: &[u8; 32]) -> Result<([u8; 32], [u8; 1088]), Error> {
        let mut key = [0u8; 32];
        let mut ct = [0u8; 1088];
        let mut scratch: Scratch = [0; 4096];
        #[cfg(target_arch = "x86_64")]
        if let Some(ekx) = self.expanded() {
            // SAFETY: `ekx`, `m`, `key`, `ct` and `scratch` are valid for
            // reads (and, for the last three, writes) of their sizes; they
            // are distinct Rust objects, so they do not overlap each other or
            // the stack, or wrap around the end of the address space. `ekx`
            // was written by `vg_mlkem768_keygen_expanded` or by
            // `vg_mlkem768_expand_ek` from a key that passed
            // `vg_mlkem768_check_ek` (or an instance of them), in a call that
            // returned 1.
            unsafe { vg_mlkem768_encaps_expanded(ekx, m, &mut key, &mut ct, &mut scratch) };
            zeroize(&mut scratch);
            return Ok((key, ct));
        }
        // SAFETY: `self.bytes`, `m`, `key`, `ct` and `scratch` are valid for
        // reads (and, for the last three, writes) of their sizes; they are
        // distinct Rust objects, so they do not overlap each other or the
        // stack, or wrap around the end of the address space. `self.bytes`
        // passed `vg_mlkem768_check_ek`. `Backend::select` chose AVX2 only
        // if the CPU has `VG_MLKEM768_ENCAPS_AVX2_FEATURES`.
        let r = unsafe {
            match Backend::select() {
                Backend::Scalar => {
                    vg_mlkem768_encaps(&self.bytes, m, &mut key, &mut ct, &mut scratch)
                }
                #[cfg(target_arch = "x86_64")]
                Backend::Avx2 => {
                    vg_mlkem768_encaps_avx2(&self.bytes, m, &mut key, &mut ct, &mut scratch)
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
            ek: EncapsulationKey768 {
                bytes: [0; 1184],
                #[cfg(target_arch = "x86_64")]
                expanded: Expanded::new(),
            },
            dk: [0; 2400],
        };
        let mut scratch: Scratch = [0; 4096];
        // SAFETY: `seed`, the expanded key's buffer, `key.dk` and `scratch`
        // are valid for reads (and, for the last three, writes) of their
        // sizes; they are distinct Rust objects, so they do not overlap each
        // other or the stack, or wrap around the end of the address space.
        // `Backend::select` chose AVX2 only if the CPU has
        // `VG_MLKEM768_KEYGEN_EXPANDED_AVX2_FEATURES`.
        #[cfg(target_arch = "x86_64")]
        let r = {
            let ekx = key.ek.expanded.buffer();
            let r = unsafe {
                match Backend::select() {
                    Backend::Scalar => {
                        vg_mlkem768_keygen_expanded(seed, ekx, &mut key.dk, &mut scratch)
                    }
                    Backend::Avx2 => {
                        vg_mlkem768_keygen_expanded_avx2(seed, ekx, &mut key.dk, &mut scratch)
                    }
                }
            };
            // The expanded key starts with the key.
            key.ek.bytes.copy_from_slice(&ekx[..1184]);
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
        #[cfg(target_arch = "x86_64")]
        key.ek.expanded.set_ready();
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
        // Key generation wrote the expanded key.
        let ekx = self.ek.expanded.ready().unwrap();
        // SAFETY: `self.dk`, `ekx`, `ct`, `key` and `scratch` are valid for
        // reads (and, for the last two, writes) of their sizes; they are
        // distinct Rust objects, so they do not overlap each other or the
        // stack, or wrap around the end of the address space. `self.dk` and
        // `ekx` were written by `vg_mlkem768_keygen_expanded` (or an instance
        // of it) in a call that returned 1.
        unsafe { vg_mlkem768_decaps_expanded(&self.dk, ekx, ct, &mut key, &mut scratch) };
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

    /// The expanded key is computed on the second use, and never if that
    /// fails; a clone keeps it.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn expands_on_second_use() {
        use super::Expanded;

        let fill = |ekx: &mut [u8; 4]| {
            *ekx = [7; 4];
            true
        };
        let e = Expanded::<4>::new();
        assert_eq!(e.clone().ready(), None);
        assert_eq!(e.get(|_| unreachable!()), None);
        assert_eq!(e.get(fill), Some(&[7; 4]));
        assert_eq!(e.get(|_| unreachable!()), Some(&[7; 4]));
        assert_eq!(e.clone().ready(), Some(&[7; 4]));
        let f = Expanded::<4>::new();
        assert_eq!(f.get(|_| unreachable!()), None);
        assert_eq!(f.get(|_| false), None);
        assert_eq!(f.get(|_| unreachable!()), None);
    }
}
