//! PBKDF2 (RFC 8018 §5.2), with HMAC as the pseudorandom function: a module
//! here for each hash function with a verified implementation.
//!
//! On x86-64 and AArch64, [`pbkdf2_hmac`] is one call of the hash's verified
//! `vg_pbkdf2_hmac_<hash>`, which derives the whole key. On the other
//! targets, for each block `Tᵢ` of the derived key, `U₁ = HMAC (P, S ‖ INT (i))`
//! is the verified HMAC (`Hmac`), and the rest of the chain,
//! `Uⱼ₊₁ = HMAC (P, Uⱼ)` exclusive-or'ed into `Tᵢ = U₁ ⊕ … ⊕ U_c`, is the
//! hash's verified `vg_pbkdf2_hmac_<hash>_iterate`, from the streaming states
//! that the HMAC computation starts from; the Rust code only splits the
//! derived key into blocks and truncates the last one.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use core::num::NonZeroU32;

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
use crate::hmac::Hmac;
use crate::hmac::HmacHash;

mod md5;
mod sha1;
mod sha224;
mod sha256;
mod sha384;
mod sha512;
mod sha512_224;
mod sha512_256;

/// A hash function with a verified PBKDF2-HMAC implementation.
pub trait Pbkdf2Hash: HmacHash {
    /// Fills `out` with the key derived from `password` and `salt` with
    /// `iterations` iterations (see [`pbkdf2_hmac`]).
    #[doc(hidden)]
    fn pbkdf2_derive(password: &[u8], salt: &[u8], iterations: NonZeroU32, out: &mut [u8]);
}

/// Fills `out` with the key derived from `password` and `salt` with
/// `iterations` iterations of PBKDF2 with HMAC over the hash function `H`.
///
/// # Panics
///
/// If `out` is longer than (2³² − 1) times the digest size ("derived key too
/// long" in RFC 8018).
pub fn pbkdf2_hmac<H: Pbkdf2Hash>(
    password: &[u8],
    salt: &[u8],
    iterations: NonZeroU32,
    out: &mut [u8],
) {
    H::pbkdf2_derive(password, salt, iterations, out);
}

/// PBKDF2 from the verified HMAC and iteration: `U₁` of each block with
/// [`Hmac`], and the rest of its chain with `iterate`, from the HMAC key's
/// streaming states `key` (`key` of the computation that has not absorbed
/// any data yet).
#[cfg(any(target_arch = "arm", target_arch = "x86"))]
fn derive_blocks<H: HmacHash, K>(
    password: &[u8],
    salt: &[u8],
    iterations: NonZeroU32,
    out: &mut [u8],
    key: impl FnOnce(&Hmac<H>) -> K,
    iterate: impl Fn(&K, &H::Output, u32, &mut H::Output),
) {
    let prf = Hmac::<H>::new(password);
    let key = key(&prf);
    for (i, block) in out.chunks_mut(H::OUTPUT_SIZE).enumerate() {
        let index = u32::try_from(i + 1).expect("PBKDF2 derived key too long");
        let mut mac = prf.clone();
        mac.update(salt);
        mac.update(&index.to_be_bytes());
        let u = mac.finalize();
        let mut t = u.clone();
        iterate(&key, &u, iterations.get() - 1, &mut t);
        block.copy_from_slice(&t.as_ref()[..block.len()]);
    }
}

/// Checks that PBKDF2 can derive `len` bytes from blocks of `block` bytes:
/// at most 2³² − 1 blocks ("derived key too long" in RFC 8018).
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn check_len(len: usize, block: usize) {
    u32::try_from(len.div_ceil(block)).expect("PBKDF2 derived key too long");
}

/// On ARMv7 and x86, makes a hash function with a streaming
/// HMAC (`crate::hmac`'s `streaming_hmac!`) a [`Pbkdf2Hash`], with its
/// verified `vg_pbkdf2_hmac_<hash>_iterate` (contract
/// `VG.Spec.Hmac.Instance.iterateContract` of the hash's `Instance`) under
/// `derive_blocks`, given its streaming state size, the function's working
/// space (in 64-bit words) and its digest size.
///
/// `iterate` is listed for each implementation of the hash, as for
/// `streaming_hmac!`, and a derivation runs the one of the implementation its
/// HMAC computation runs: the `match` is exhaustive, so a new implementation
/// of the hash does not compile until it is listed here too, and a test
/// checks that it needs no CPU feature the hash's implementation was not
/// selected for.
#[cfg(any(target_arch = "arm", target_arch = "x86"))]
macro_rules! streaming_pbkdf2 {
    (
        $hash:ident ($backend:ident) {
            $base:ident => $iterate:path
            $(, $(#[$attr:meta])* $variant:ident if [$($req:path),*] => $viterate:path)*
            $(,)?
        },
        state: $state:literal,
        scratch: $scratch:literal,
        output: $output:literal $(,)?
    ) => {
        // The CPU features of each implementation, which `tests` checks.
        $(
            $(#[$attr])*
            const _: &[&[&str]] = &[$($req),*];
        )*

        /// The streaming states for `K₀ ⊕ ipad` and `K₀ ⊕ opad`, and the
        /// implementation of the hash the HMAC computation runs.
        struct Key {
            states: [u8; 2 * $state],
            backend: $backend,
        }

        impl Drop for Key {
            fn drop(&mut self) {
                $crate::zeroize::zeroize(&mut self.states);
            }
        }

        /// The streaming states of an HMAC computation that has not absorbed
        /// any data yet, and the implementation of the hash it runs.
        fn key(prf: &crate::hmac::Hmac<$hash>) -> Key {
            let (inner, count) = prf.state().inner.state();
            debug_assert_eq!(count, <$hash>::BLOCK_SIZE as u64);
            let mut states = [0; 2 * $state];
            states[..$state].copy_from_slice(&inner);
            states[$state..].copy_from_slice(&prf.state().outer);
            Key { states, backend: prf.state().inner.backend() }
        }

        /// Repeats `U ← HMAC (K₀, U)`, `T ← T ⊕ U` `n` times, from `U = *u`
        /// and `T = *t`, leaving the final `T` in `*t`.
        fn iterate(key: &Key, u: &[u8; $output], n: u32, t: &mut [u8; $output]) {
            let iterate = match key.backend {
                $backend::$base => $iterate,
                $($(#[$attr])* $backend::$variant => $viterate,)*
            };
            let mut scratch = [0u64; $scratch];
            // SAFETY: `key.states` is valid for reads of both streaming
            // states, `u` for reads of a digest, `t` for reads and writes
            // of one and `scratch` for reads and writes of its size; `t`
            // and `scratch` are distinct objects from each other and the
            // others (`key` and `u` are only read), so none of them
            // overlaps another written one or the call's stack frame,
            // and, as Rust objects, none wraps around the address space.
            // `key.states` holds the streaming states for `K₀ ⊕ ipad` and
            // `K₀ ⊕ opad` that the hash's HMAC `init` left. `iterate`
            // needs no CPU feature that `key.backend` was not selected
            // for (`tests::backend_features`).
            unsafe { iterate(&key.states, u, n, t, &mut scratch) };
        }

        impl super::Pbkdf2Hash for $hash {
            fn pbkdf2_derive(
                password: &[u8],
                salt: &[u8],
                iterations: core::num::NonZeroU32,
                out: &mut [u8],
            ) {
                super::derive_blocks::<$hash, Key>(password, salt, iterations, out, key, iterate);
            }
        }

        #[cfg(test)]
        mod tests {
            #[allow(unused_imports)]
            use super::*;

            /// Each implementation's `iterate` needs no CPU feature that the
            /// hash's implementation is not selected for: on every set of
            /// features that selects it.
            #[test]
            fn backend_features() {
                $(
                    $(#[$attr])*
                    for bits in 0..1u32 << $crate::cpu::NAMES.len() {
                        let f = $crate::cpu::Features(bits);
                        if $backend::select(f) == $backend::$variant {
                            assert!(f.contains($crate::cpu::Features::all(&[$($req),*])));
                        }
                    }
                )*
            }
        }
    };
}

#[cfg(any(target_arch = "arm", target_arch = "x86"))]
use streaming_pbkdf2;

/// On x86-64 and AArch64, makes a hash function a [`Pbkdf2Hash`] with its verified
/// `vg_pbkdf2_hmac_<hash>` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract`
/// of the hash's `Instance`), which derives the whole key, given the
/// function's working space (in 64-bit words) and the digest size.
///
/// `pbkdf2` is listed for each implementation of the hash (its backend
/// enum's variants, with the CPU features it needs), and a derivation runs
/// the one of the implementation selected for this CPU, as the hash and its
/// HMAC do: the `match` on the backend is exhaustive, so a new
/// implementation of the hash does not compile until it is listed here too
/// (see "Variants and generic callers" in
/// `lean/VerifiedGarbage/TCB/Emit.lean`), and a test checks that it needs no
/// CPU feature the hash's implementation was not selected for.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
macro_rules! whole_pbkdf2 {
    (
        $hash:ident ($backend:ident) {
            $base:ident => $pbkdf2:path
            $(, $(#[$attr:meta])* $variant:ident if [$($req:path),*] => $vpbkdf2:path)*
            $(,)?
        },
        scratch: $scratch:literal,
        output: $output:literal $(,)?
    ) => {
        // The CPU features of each implementation, which `tests` checks.
        $(
            $(#[$attr])*
            const _: &[&[&str]] = &[$($req),*];
        )*

        impl super::Pbkdf2Hash for $hash {
            fn pbkdf2_derive(
                password: &[u8],
                salt: &[u8],
                iterations: core::num::NonZeroU32,
                out: &mut [u8],
            ) {
                super::check_len(out.len(), $output);
                let pbkdf2 = match $backend::select($crate::cpu::detected()) {
                    $backend::$base => $pbkdf2,
                    $($(#[$attr])* $backend::$variant => $vpbkdf2,)*
                };
                let mut scratch = [0u64; $scratch];
                // SAFETY: `iterations` is positive and `out.len()` at most
                // (2³² − 1) times the digest size; `password` and `salt` are
                // valid for reads of their lengths, `out` for reads and
                // writes of its length and `scratch` for reads and writes of
                // its size; `out` and `scratch` are distinct objects from
                // each other and the others (`password` and `salt` are only
                // read), so none of them overlaps another written one or the
                // call's stack frame, and, as Rust objects, none wraps
                // around the address space. `pbkdf2` needs no CPU feature
                // that the implementation was not selected for
                // (`tests::backend_features`).
                unsafe {
                    pbkdf2(
                        password.as_ptr(),
                        password.len(),
                        salt.as_ptr(),
                        salt.len(),
                        iterations.get(),
                        out.as_mut_ptr(),
                        out.len(),
                        &mut scratch,
                    )
                };
            }
        }

        #[cfg(test)]
        mod tests {
            #[allow(unused_imports)]
            use super::*;

            /// Each implementation's `pbkdf2` needs no CPU feature that the
            /// hash's implementation is not selected for: on every set of
            /// features that selects it.
            #[test]
            fn backend_features() {
                $(
                    $(#[$attr])*
                    for bits in 0..1u32 << $crate::cpu::NAMES.len() {
                        let f = $crate::cpu::Features(bits);
                        if $backend::select(f) == $backend::$variant {
                            assert!(f.contains($crate::cpu::Features::all(&[$($req),*])));
                        }
                    }
                )*
            }
        }
    };
}

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use whole_pbkdf2;
