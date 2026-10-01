//! What ML-DSA-44, ML-DSA-65 and ML-DSA-87 (`crate::mldsa44`,
//! `crate::mldsa65`, `crate::mldsa87`) share: their API, defined once by
//! `ml_dsa!` for each parameter set's verified functions and sizes.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

/// The message representative `μ = H(tr ‖ M′, 64)` (FIPS 204 Algorithm 7,
/// line 6) of the message `msg` with the context string `ctx`, formatted as
/// `M′ = 0 ‖ |ctx| ‖ ctx ‖ msg` (Algorithm 2, line 10), for the public key
/// hash `tr`; `None` if `ctx` is longer than 255 bytes.
pub(crate) fn message_rep(tr: &[u8; 64], msg: &[u8], ctx: &[u8]) -> Option<[u8; 64]> {
    let len = u8::try_from(ctx.len()).ok()?;
    let mut h = crate::hashes::sha3::Shake256::new();
    h.update(tr);
    h.update(&[0, len]);
    h.update(ctx);
    h.update(msg);
    let mut mu = [0u8; 64];
    h.finalize(&mut mu);
    Some(mu)
}

/// Defines the API of one ML-DSA parameter set: its `Error`, `SigningKey`
/// and `VerifyingKey`, over its verified `keygen`, `sign` and `verify`
/// functions (which take `μ`) and its sizes.
macro_rules! ml_dsa {
    (
        name: $name:literal,
        signing_key: $SigningKey:ident,
        verifying_key: $VerifyingKey:ident,
        keygen: $keygen:path,
        sign: $sign:path,
        verify: $verify:path,
        pk: $pk:literal,
        sk: $sk:literal,
        sig: $sig:literal,
        scratch: $scratch:literal $(,)?
    ) => {
        use $crate::mldsa_common::message_rep;
        use $crate::zeroize::zeroize;

        /// Why an operation failed.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum Error {
            /// A loop reached its bound (FIPS 204 Appendix C), which happens
            /// with probability about 2⁻²⁵⁶ or less.
            LoopBound,
            /// The context string is longer than 255 bytes (FIPS 204
            /// Algorithms 2 and 3).
            ContextTooLong,
            /// The signature is not valid.
            InvalidSignature,
            /// The operating system's random number generator failed.
            Randomness,
        }

        /// The working space of the assembly functions.
        type Scratch = [u64; $scratch];

        #[doc = concat!("An ", $name, " public key.")]
        #[derive(Clone, PartialEq, Eq)]
        pub struct $VerifyingKey {
            bytes: [u8; $pk],
            /// `tr = H(pk, 64)`.
            tr: [u8; 64],
        }

        impl core::fmt::Debug for $VerifyingKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($VerifyingKey)).finish_non_exhaustive()
            }
        }

        impl $VerifyingKey {
            /// The size of a public key, in bytes.
            pub const SIZE: usize = $pk;
            /// The size of a signature, in bytes.
            pub const SIGNATURE_SIZE: usize = $sig;

            /// The public key `bytes` (every byte string of this size is
            /// one).
            pub fn from_bytes(bytes: &[u8; $pk]) -> Self {
                let mut tr = [0u8; 64];
                $crate::hashes::sha3::Shake256::digest(bytes, &mut tr);
                $VerifyingKey { bytes: *bytes, tr }
            }

            /// The bytes of the key.
            pub fn as_bytes(&self) -> &[u8; $pk] {
                &self.bytes
            }

            /// `ML-DSA.Verify(pk, M, σ, ctx)` (FIPS 204 Algorithm 3):
            /// whether `sig` is a valid signature of the message `msg` with
            /// the context string `ctx`. Fails with
            /// [`Error::InvalidSignature`] if it is not (or, with probability
            /// about 2⁻²⁵⁶ or less, if a loop reaches its bound), and
            /// [`Error::ContextTooLong`] if `ctx` is longer than 255 bytes.
            pub fn verify(&self, msg: &[u8], ctx: &[u8], sig: &[u8; $sig]) -> Result<(), Error> {
                let mu = message_rep(&self.tr, msg, ctx).ok_or(Error::ContextTooLong)?;
                self.verify_internal(&mu, sig)
            }

            /// `ML-DSA.Verify_internal` (FIPS 204 Algorithm 8) with the
            /// message representative `mu` = `μ` given: for known-answer
            /// tests.
            #[doc(hidden)]
            pub fn verify_internal(&self, mu: &[u8; 64], sig: &[u8; $sig]) -> Result<(), Error> {
                let mut scratch: Scratch = [0; $scratch];
                // SAFETY: `self.bytes`, `mu`, `sig` and `scratch` are valid
                // for reads (and, for `scratch`, writes) of their sizes; they
                // are distinct Rust objects, so they do not overlap each other
                // or the stack, or wrap around the end of the address space.
                let r = unsafe { $verify(&self.bytes, mu, sig, &mut scratch) };
                if r == 1 { Ok(()) } else { Err(Error::InvalidSignature) }
            }
        }

        #[doc = concat!(
            "An ", $name, " private key, kept as the 32-byte seed `ξ` it is generated from \
            (FIPS 204 §3.6.3), with the keys it expands to. The seed and the expanded key are \
            destroyed when it is dropped."
        )]
        pub struct $SigningKey {
            seed: [u8; 32],
            vk: $VerifyingKey,
            sk: [u8; $sk],
        }

        impl core::fmt::Debug for $SigningKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($SigningKey)).finish_non_exhaustive()
            }
        }

        impl Drop for $SigningKey {
            fn drop(&mut self) {
                zeroize(&mut self.seed);
                zeroize(&mut self.sk);
            }
        }

        impl $SigningKey {
            /// The size of a seed, in bytes.
            pub const SEED_SIZE: usize = 32;

            /// The key pair of the seed `ξ`: `ML-DSA.KeyGen_internal(ξ)`
            /// (FIPS 204 Algorithm 6). The seed must be 32 random bytes from
            /// an approved RBG (FIPS 204 §3.6.1, Algorithm 1), or a seed so
            /// generated before.
            pub fn from_seed(seed: &[u8; 32]) -> Result<Self, Error> {
                let mut key = $SigningKey {
                    seed: *seed,
                    vk: $VerifyingKey { bytes: [0; $pk], tr: [0; 64] },
                    sk: [0; $sk],
                };
                let mut scratch: Scratch = [0; $scratch];
                // SAFETY: `seed`, `key.vk.bytes`, `key.sk` and `scratch` are
                // valid for reads (and, for the last three, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `seed` is the caller's seed.
                let r = unsafe { $keygen(seed, &mut key.vk.bytes, &mut key.sk, &mut scratch) };
                zeroize(&mut scratch);
                if r != 1 {
                    // A loop reaches its bound with probability about 2^-256
                    // or less; dropping `key` destroys it.
                    // NO-COVERAGE-START
                    return Err(Error::LoopBound);
                    // NO-COVERAGE-END
                }
                // `tr` is bytes 64–127 of the private key (FIPS 204
                // Algorithm 24).
                key.vk.tr.copy_from_slice(&key.sk[64..128]);
                Ok(key)
            }

            /// The seed `ξ`.
            pub fn seed(&self) -> &[u8; 32] {
                &self.seed
            }

            /// The public key.
            pub fn verifying_key(&self) -> &$VerifyingKey {
                &self.vk
            }

            /// `ML-DSA.Sign(sk, M, ctx)` (FIPS 204 Algorithm 2), hedged: a
            /// signature of the message `msg` with the context string `ctx`,
            /// with 32 bytes of randomness from the operating system. Fails
            /// with [`Error::ContextTooLong`] if `ctx` is longer than 255
            /// bytes.
            pub fn sign(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], Error> {
                let mut rnd = [0u8; 32];
                if getrandom::fill(&mut rnd).is_err() {
                    // The operating system's generator does not fail in the
                    // tests.
                    // NO-COVERAGE-START
                    return Err(Error::Randomness);
                    // NO-COVERAGE-END
                }
                let r = self.sign_with(msg, ctx, &rnd);
                zeroize(&mut rnd);
                r
            }

            /// The deterministic variant of `ML-DSA.Sign(sk, M, ctx)` (FIPS
            /// 204 Algorithm 2, with `rnd` = 32 zero bytes). FIPS 204 §3.4
            /// recommends the hedged [`sign`](Self::sign) where side channels
            /// are a concern.
            pub fn sign_deterministic(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], Error> {
                self.sign_with(msg, ctx, &[0; 32])
            }

            fn sign_with(&self, msg: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Result<[u8; $sig], Error> {
                let mu = message_rep(&self.vk.tr, msg, ctx).ok_or(Error::ContextTooLong)?;
                self.sign_internal(&mu, rnd)
            }

            /// `ML-DSA.Sign_internal` (FIPS 204 Algorithm 7) with the
            /// message representative `mu` = `μ` and the randomness `rnd`
            /// given: for known-answer tests only. `rnd` must otherwise be
            /// fresh random bytes, which [`sign`](Self::sign) draws.
            #[doc(hidden)]
            pub fn sign_internal(&self, mu: &[u8; 64], rnd: &[u8; 32]) -> Result<[u8; $sig], Error> {
                let mut sig = [0u8; $sig];
                let mut scratch: Scratch = [0; $scratch];
                // SAFETY: `self.sk`, `mu`, `rnd`, `sig` and `scratch` are
                // valid for reads (and, for the last two, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `self.sk` was written by the key
                // generation.
                let r = unsafe { $sign(&self.sk, mu, rnd, &mut sig, &mut scratch) };
                zeroize(&mut scratch);
                if r != 1 {
                    // A loop reaches its bound with probability about 2^-256
                    // or less.
                    // NO-COVERAGE-START
                    zeroize(&mut sig);
                    return Err(Error::LoopBound);
                    // NO-COVERAGE-END
                }
                Ok(sig)
            }
        }
    };
}

pub(crate) use ml_dsa;

#[cfg(test)]
mod tests {
    use super::message_rep;

    #[test]
    fn context_too_long() {
        assert!(message_rep(&[0; 64], b"", &[0; 255]).is_some());
        assert!(message_rep(&[0; 64], b"", &[0; 256]).is_none());
    }
}
