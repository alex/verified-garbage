//! PBKDF2 (RFC 8018 §5.2), with HMAC as the pseudorandom function: a module
//! here for each hash function with a verified implementation.
//!
//! [`pbkdf2_hmac`] is one call of the hash's verified `vg_pbkdf2_hmac_<hash>`,
//! which derives the whole key.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use core::num::NonZeroU32;

use crate::hmac::HmacHash;

mod md5;
mod sha1;
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

/// Checks that PBKDF2 can derive `len` bytes from blocks of `block` bytes:
/// at most 2³² − 1 blocks ("derived key too long" in RFC 8018).
fn check_len(len: usize, block: usize) {
    u32::try_from(len.div_ceil(block)).expect("PBKDF2 derived key too long");
}

/// Makes a hash function a [`Pbkdf2Hash`] with its verified
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

use whole_pbkdf2;
