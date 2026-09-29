//! PBKDF2 (RFC 8018 §5.2), with HMAC as the pseudorandom function: a module
//! here for each hash function with a verified implementation.
//!
//! For each block `Tᵢ` of the derived key, `U₁ = HMAC (P, S ‖ INT (i))` is
//! the verified HMAC ([`Hmac`]), and the rest of the chain,
//! `Uⱼ₊₁ = HMAC (P, Uⱼ)` exclusive-or'ed into `Tᵢ = U₁ ⊕ … ⊕ U_c`, is the
//! hash's verified `vg_pbkdf2_hmac_<hash>_iterate` ([`Pbkdf2Hash`]), from
//! the streaming states that the HMAC computation starts from.
//! [`pbkdf2_hmac`] only splits the derived key into blocks and truncates the
//! last one, unless the hash has a verified implementation of the whole
//! function (SHA-256 on x86-64, `vg_pbkdf2_hmac_sha256`), which it then calls
//! once instead (`Pbkdf2Hash::pbkdf2_derive`).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use core::num::NonZeroU32;

use crate::hmac::{Hmac, HmacHash};

mod md5;
mod sha1;
mod sha256;
mod sha384;
mod sha512;
mod sha512_224;
mod sha512_256;

pub use sha256::pbkdf2_hmac_sha256;

/// A hash function with a verified PBKDF2-HMAC iteration.
pub trait Pbkdf2Hash: HmacHash {
    /// The streaming states of the two HMAC keys, `K₀ ⊕ ipad` and then
    /// `K₀ ⊕ opad`.
    #[doc(hidden)]
    type Key;
    /// The keys of an HMAC computation that has not absorbed any data yet
    /// (and, if the hash has several implementations, which one it runs).
    #[doc(hidden)]
    fn pbkdf2_key(prf: &Hmac<Self>) -> Self::Key;
    /// Repeats `U ← HMAC (K₀, U)`, `T ← T ⊕ U` `n` times, from `U = *u` and
    /// `T = *t`, leaving the final `T` in `*t`.
    #[doc(hidden)]
    fn pbkdf2_iterate(key: &Self::Key, u: &Self::Output, n: u32, t: &mut Self::Output);
    /// Fills `out` with the key derived from `password` and `salt` with
    /// `iterations` iterations: block by block with the HMAC computation and
    /// `Pbkdf2Hash::pbkdf2_iterate`, unless the hash has a verified
    /// implementation of the whole function.
    #[doc(hidden)]
    fn pbkdf2_derive(password: &[u8], salt: &[u8], iterations: NonZeroU32, out: &mut [u8]) {
        derive_blocks::<Self>(password, salt, iterations, out);
    }
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

/// [`pbkdf2_hmac`] block by block: `U₁` with the verified HMAC, the rest of
/// each block's chain with the hash's verified iteration.
fn derive_blocks<H: Pbkdf2Hash>(
    password: &[u8],
    salt: &[u8],
    iterations: NonZeroU32,
    out: &mut [u8],
) {
    let prf = Hmac::<H>::new(password);
    let key = H::pbkdf2_key(&prf);
    for (i, block) in out.chunks_mut(H::OUTPUT_SIZE).enumerate() {
        let index = u32::try_from(i + 1).expect("PBKDF2 derived key too long");
        let mut mac = prf.clone();
        mac.update(salt);
        mac.update(&index.to_be_bytes());
        let u = mac.finalize();
        let mut t = u.clone();
        H::pbkdf2_iterate(&key, &u, iterations.get() - 1, &mut t);
        block.copy_from_slice(&t.as_ref()[..block.len()]);
    }
}

/// Makes a hash function with a streaming HMAC (`crate::hmac`'s
/// `streaming_hmac!`) a [`Pbkdf2Hash`], with its verified
/// `vg_pbkdf2_hmac_<hash>_iterate` (contract
/// `VG.Spec.Hmac.Instance.iterateContract` of the hash's `Instance`), given
/// its streaming state size, the function's working space (in 64-bit words)
/// and its digest size.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
macro_rules! streaming_pbkdf2 {
    (
        $hash:ident: $iterate:path,
        state: $state:literal,
        scratch: $scratch:literal,
        output: $output:literal $(,)?
    ) => {
        impl super::Pbkdf2Hash for $hash {
            type Key = [u8; 2 * $state];

            fn pbkdf2_key(prf: &crate::hmac::Hmac<Self>) -> [u8; 2 * $state] {
                let (inner, count) = prf.state().inner.state();
                debug_assert_eq!(count, Self::BLOCK_SIZE as u64);
                let mut key = [0; 2 * $state];
                key[..$state].copy_from_slice(&inner);
                key[$state..].copy_from_slice(&prf.state().outer);
                key
            }

            fn pbkdf2_iterate(
                key: &[u8; 2 * $state],
                u: &[u8; $output],
                n: u32,
                t: &mut [u8; $output],
            ) {
                let mut scratch = [0u64; $scratch];
                // SAFETY: `key` is valid for reads of both streaming states,
                // `u` for reads of a digest, `t` for reads and writes of one
                // and `scratch` for reads and writes of its size; `t` and
                // `scratch` are distinct objects from each other and the
                // others (`key` and `u` are only read), so none of them
                // overlaps another written one or the call's stack frame,
                // and, as Rust objects, none wraps around the address space.
                // `key` holds the streaming states for `K₀ ⊕ ipad` and
                // `K₀ ⊕ opad` that the hash's HMAC `init` left.
                unsafe { $iterate(key, u, n, t, &mut scratch) };
            }
        }
    };
}

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use streaming_pbkdf2;
