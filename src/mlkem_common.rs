//! What ML-KEM-768 and ML-KEM-1024 (`crate::mlkem768`, `crate::mlkem1024`)
//! share: their `Error`, and their API, defined once by `ml_kem!` for each
//! parameter set's verified functions and sizes.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

/// Why an operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// A `SampleNTT` reached the bound on its loop's iterations (FIPS 203
    /// Appendix B), which happens with probability less than 2⁻²⁶¹ for each
    /// call: less than 2⁻²⁵⁸ in an ML-KEM-768 operation (9 calls) and 2⁻²⁵⁷
    /// in an ML-KEM-1024 one (16 calls).
    SampleBound,
    /// The encapsulation key failed the check of FIPS 203 §7.2.
    InvalidKey,
    /// The operating system's random number generator failed.
    Randomness,
}

/// The implementations key generation, encapsulation and decapsulation
/// follow: each has an instance calling each of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The target's baseline ISA (on x86-64, `SampleNTT` on one seed at a
    /// time; elsewhere, one entry of the matrix at a time), with scalar
    /// Keccak.
    Scalar,
    /// AArch64 with the SHA-3 extension, for Keccak.
    #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
    Sha3,
    /// AVX2: four instances of SHAKE128 at once.
    #[cfg(target_arch = "x86_64")]
    Avx2,
}

impl Backend {
    /// The best implementation, on a CPU with the features `f`, of functions
    /// whose AVX2 instances need `avx2` and whose SHA-3 instances need
    /// `sha3`: on AArch64, the Keccak implementation the SHA-3 functions use
    /// (`crate::hashes::sha3::Backend::detected`, which chooses SHA-3 only
    /// with the `cpu-features-env` feature, when `VG_CPU_FEATURES` asks for
    /// `sha3`) if the CPU has `sha3`; on x86-64, AVX2 if it has `avx2`.
    // Each target uses only some of the arguments.
    #[allow(unused_variables)]
    pub(crate) fn select(
        f: crate::cpu::Features,
        avx2: crate::cpu::Features,
        sha3: crate::cpu::Features,
    ) -> Backend {
        #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
        if !f.contains(sha3) {
            return Backend::Scalar;
        }
        match crate::hashes::sha3::Backend::detected() {
            crate::hashes::sha3::Backend::Scalar => {
                #[cfg(target_arch = "x86_64")]
                if f.contains(avx2) {
                    return Backend::Avx2;
                }
                Backend::Scalar
            }
            #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
            crate::hashes::sha3::Backend::Sha3 => Backend::Sha3,
        }
    }
}

/// Defines the API of one ML-KEM parameter set: its `EncapsulationKey` and
/// `DecapsulationKey`, over its verified `check_ek`, `keygen`, `encaps` and
/// `decaps` functions (and their SHA-3 and AVX2 instances, with the
/// features they need), its sizes, and the number of `SampleNTT` calls in
/// each operation with the bound on the probability that one reaches its
/// loop's bound (for the comments).
macro_rules! ml_kem {
    (
        name: $name:literal,
        encapsulation_key: $EncapsulationKey:ident,
        decapsulation_key: $DecapsulationKey:ident,
        check_ek: $check_ek:path,
        keygen: $keygen:path,
        encaps: $encaps:path,
        decaps: $decaps:path,
        keygen_sha3: ($keygen_sha3:path, $keygen_sha3_features:path),
        encaps_sha3: ($encaps_sha3:path, $encaps_sha3_features:path),
        decaps_sha3: ($decaps_sha3:path, $decaps_sha3_features:path),
        keygen_avx2: ($keygen_avx2:path, $keygen_avx2_features:path),
        encaps_avx2: ($encaps_avx2:path, $encaps_avx2_features:path),
        decaps_avx2: ($decaps_avx2:path, $decaps_avx2_features:path),
        ek: $ek:literal,
        dk: $dk:literal,
        ct: $ct:literal,
        scratch: $scratch:literal $(,)?
    ) => {
        pub use $crate::mlkem_common::Error;
        use $crate::mlkem_common::Backend;
        use $crate::zeroize::zeroize;

        /// The implementation to call: the best one whose instances of key
        /// generation, encapsulation and decapsulation the CPU can all run.
        fn backend() -> Backend {
            #[cfg(target_arch = "x86_64")]
            const AVX2: &[$crate::cpu::Features] =
                &[$keygen_avx2_features, $encaps_avx2_features, $decaps_avx2_features];
            #[cfg(not(target_arch = "x86_64"))]
            const AVX2: &[$crate::cpu::Features] = &[];
            #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
            const SHA3: &[$crate::cpu::Features] =
                &[$keygen_sha3_features, $encaps_sha3_features, $decaps_sha3_features];
            #[cfg(not(all(target_arch = "aarch64", feature = "cpu-features-env")))]
            const SHA3: &[$crate::cpu::Features] = &[];
            Backend::select(
                $crate::cpu::detected(),
                const { $crate::cpu::Features::all(AVX2) },
                const { $crate::cpu::Features::all(SHA3) },
            )
        }

        /// The working space of the assembly functions.
        type Scratch = [u64; $scratch];

        #[doc = concat!("An ", $name, " encapsulation key, which passed the check of FIPS 203 §7.2.")]
        #[derive(Clone, PartialEq, Eq)]
        pub struct $EncapsulationKey {
            bytes: [u8; $ek],
        }

        impl core::fmt::Debug for $EncapsulationKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($EncapsulationKey)).finish_non_exhaustive()
            }
        }

        impl $EncapsulationKey {
            /// The size of an encapsulation key, in bytes.
            pub const SIZE: usize = $ek;
            /// The size of a ciphertext, in bytes.
            pub const CIPHERTEXT_SIZE: usize = $ct;
            /// The size of a shared secret key, in bytes.
            pub const SHARED_KEY_SIZE: usize = 32;

            /// The encapsulation key `bytes`, if it passes the encapsulation
            /// key check of FIPS 203 §7.2 (every integer it encodes is less
            /// than `q`); [`Error::InvalidKey`] otherwise.
            pub fn from_bytes(bytes: &[u8; $ek]) -> Result<Self, Error> {
                // SAFETY: `bytes` is valid for reads of its size, and a Rust
                // object, so it does not overlap the stack or wrap around the
                // end of the address space.
                if unsafe { $check_ek(bytes) } == 1 {
                    Ok($EncapsulationKey { bytes: *bytes })
                } else {
                    Err(Error::InvalidKey)
                }
            }

            /// The bytes of the key.
            pub fn as_bytes(&self) -> &[u8; $ek] {
                &self.bytes
            }

            /// `ML-KEM.Encaps` (FIPS 203 Algorithm 20): a shared secret key
            /// and its ciphertext, with 32 bytes of randomness from the
            /// operating system.
            pub fn encapsulate(&self) -> Result<([u8; 32], [u8; $ct]), Error> {
                let mut m = [0u8; 32];
                if getrandom::fill(&mut m).is_err() {
                    // The operating system's generator does not fail in the
                    // tests.
                    // NO-COVERAGE-START
                    return Err(Error::Randomness);
                    // NO-COVERAGE-END
                }
                let r = self.encapsulate_internal(&m);
                zeroize(&mut m);
                r
            }

            /// `ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17), with
            /// the randomness `m`: for known-answer tests only. FIPS 203 §6
            /// allows this function only for testing; `m` must otherwise be
            /// fresh random bytes from an approved RBG, which
            /// [`encapsulate`](Self::encapsulate) draws.
            #[doc(hidden)]
            pub fn encapsulate_internal(&self, m: &[u8; 32]) -> Result<([u8; 32], [u8; $ct]), Error> {
                let mut key = [0u8; 32];
                let mut ct = [0u8; $ct];
                let mut scratch: Scratch = [0; $scratch];
                // SAFETY: `self.bytes`, `m`, `key`, `ct` and `scratch` are
                // valid for reads (and, for the last three, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `self.bytes` passed the encapsulation
                // key check. `backend()` chose an implementation whose
                // features the CPU has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $encaps(&self.bytes, m, &mut key, &mut ct, &mut scratch),
                        #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
                        Backend::Sha3 => $encaps_sha3(&self.bytes, m, &mut key, &mut ct, &mut scratch),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $encaps_avx2(&self.bytes, m, &mut key, &mut ct, &mut scratch),
                    }
                };
                zeroize(&mut scratch);
                if r != 1 {
                    // A `SampleNTT` reaches its bound with the probability
                    // the module's documentation gives.
                    // NO-COVERAGE-START
                    zeroize(&mut key);
                    zeroize(&mut ct);
                    return Err(Error::SampleBound);
                    // NO-COVERAGE-END
                }
                Ok((key, ct))
            }
        }

        #[doc = concat!(
            "An ", $name, " decapsulation key, kept as the seed `d ‖ z` it is generated from, \
            with the keys it expands to. The seed and the expanded key are destroyed when it is \
            dropped."
        )]
        pub struct $DecapsulationKey {
            seed: [u8; 64],
            ek: $EncapsulationKey,
            dk: [u8; $dk],
        }

        impl core::fmt::Debug for $DecapsulationKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($DecapsulationKey)).finish_non_exhaustive()
            }
        }

        impl Drop for $DecapsulationKey {
            fn drop(&mut self) {
                zeroize(&mut self.seed);
                zeroize(&mut self.dk);
            }
        }

        impl $DecapsulationKey {
            /// The size of a seed, in bytes.
            pub const SEED_SIZE: usize = 64;

            /// The key pair of the seed `d ‖ z` (`d` its first 32 bytes, `z`
            /// the last 32): `ML-KEM.KeyGen_internal(d, z)` (FIPS 203
            /// Algorithm 16). The seed must be 64 random bytes from an
            /// approved RBG (FIPS 203 §3.3, Algorithm 19), or a seed so
            /// generated before.
            pub fn from_seed(seed: &[u8; 64]) -> Result<Self, Error> {
                let mut key = $DecapsulationKey {
                    seed: *seed,
                    ek: $EncapsulationKey { bytes: [0; $ek] },
                    dk: [0; $dk],
                };
                let mut scratch: Scratch = [0; $scratch];
                // SAFETY: `seed`, `key.ek.bytes`, `key.dk` and `scratch` are
                // valid for reads (and, for the last three, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `backend()` chose an implementation
                // whose features the CPU has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $keygen(seed, &mut key.ek.bytes, &mut key.dk, &mut scratch),
                        #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
                        Backend::Sha3 => $keygen_sha3(seed, &mut key.ek.bytes, &mut key.dk, &mut scratch),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $keygen_avx2(seed, &mut key.ek.bytes, &mut key.dk, &mut scratch),
                    }
                };
                zeroize(&mut scratch);
                if r != 1 {
                    // A `SampleNTT` reaches its bound with the probability
                    // the module's documentation gives; dropping `key`
                    // destroys it.
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
            pub fn encapsulation_key(&self) -> &$EncapsulationKey {
                &self.ek
            }

            /// `ML-KEM.Decaps` (FIPS 203 Algorithm 21): the shared secret key
            /// of the ciphertext `ct`, which is the implicit rejection key
            /// `J(z ‖ ct)` if `ct` is not a ciphertext of this key (in
            /// constant time: nothing tells whether it was rejected).
            pub fn decapsulate(&self, ct: &[u8; $ct]) -> Result<[u8; 32], Error> {
                let mut key = [0u8; 32];
                let mut scratch: Scratch = [0; $scratch];
                // SAFETY: `self.dk`, `ct`, `key` and `scratch` are valid for
                // reads (and, for the last two, writes) of their sizes; they
                // are distinct Rust objects, so they do not overlap each
                // other or the stack, or wrap around the end of the address
                // space. `self.dk` was written by the key generation.
                // `backend()` chose an implementation whose features the CPU
                // has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $decaps(&self.dk, ct, &mut key, &mut scratch),
                        #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
                        Backend::Sha3 => $decaps_sha3(&self.dk, ct, &mut key, &mut scratch),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $decaps_avx2(&self.dk, ct, &mut key, &mut scratch),
                    }
                };
                zeroize(&mut scratch);
                if r != 1 {
                    // A `SampleNTT` reaches its bound with the probability
                    // the module's documentation gives.
                    // NO-COVERAGE-START
                    zeroize(&mut key);
                    return Err(Error::SampleBound);
                    // NO-COVERAGE-END
                }
                Ok(key)
            }
        }
    };
}

pub(crate) use ml_kem;
