//! PBKDF2 (RFC 8018 §5.2) with HMAC as the pseudorandom function.
//!
//! For each block `Tᵢ` of the derived key, `U₁ = HMAC (P, S ‖ INT (i))` is
//! the verified HMAC ([`Hmac`]), and the rest of the chain,
//! `Uⱼ₊₁ = HMAC (P, Uⱼ)` exclusive-or'ed into `Tᵢ = U₁ ⊕ … ⊕ U_c`, is the
//! verified `vg_pbkdf2_hmac_<hash>_iterate`, from the streaming states that
//! the HMAC computation starts from: `vg_pbkdf2_hmac_sha256_iterate`
//! (contract `VG.Spec.Pbkdf2.iterateSha256Contract`) and, on x86-64, those
//! for SHA-1, MD5, SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (contract
//! `VG.Spec.Hmac.Instance.iterateContract` of the hash's `Instance`, e.g.
//! `VG.Spec.Hmac.sha512I`). This module only splits the derived key into
//! blocks and truncates the last one.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use core::num::NonZeroU32;

#[cfg(target_arch = "aarch64")]
use crate::asm::aarch64::pbkdf2::vg_pbkdf2_hmac_sha256_iterate;
#[cfg(target_arch = "arm")]
use crate::asm::arm::pbkdf2::vg_pbkdf2_hmac_sha256_iterate;
#[cfg(target_arch = "x86_64")]
use crate::asm::x86_64::pbkdf2::{
    vg_pbkdf2_hmac_md5_iterate, vg_pbkdf2_hmac_sha1_iterate, vg_pbkdf2_hmac_sha256_iterate,
    vg_pbkdf2_hmac_sha384_iterate, vg_pbkdf2_hmac_sha512_224_iterate,
    vg_pbkdf2_hmac_sha512_256_iterate, vg_pbkdf2_hmac_sha512_iterate,
};
use crate::hashes::sha256::Sha256;
#[cfg(target_arch = "x86_64")]
use crate::hashes::{
    md5::Md5,
    sha1::Sha1,
    sha512::{Sha384, Sha512, Sha512_224, Sha512_256},
};
use crate::hmac::{Hmac, HmacHash};

/// A hash function with a verified PBKDF2-HMAC iteration.
pub trait Pbkdf2Hash: HmacHash {
    /// The streaming states of the two HMAC keys, `K₀ ⊕ ipad` and then
    /// `K₀ ⊕ opad`.
    #[doc(hidden)]
    type Key;
    /// The keys of an HMAC computation that has not absorbed any data yet.
    #[doc(hidden)]
    fn pbkdf2_key(prf: &Hmac<Self>) -> Self::Key;
    /// Repeats `U ← HMAC (K₀, U)`, `T ← T ⊕ U` `n` times, from `U = *u` and
    /// `T = *t`, leaving the final `T` in `*t`.
    #[doc(hidden)]
    fn pbkdf2_iterate(key: &Self::Key, u: &Self::Output, n: u32, t: &mut Self::Output);
}

impl Pbkdf2Hash for Sha256 {
    type Key = [u8; 192];

    fn pbkdf2_key(prf: &Hmac<Self>) -> [u8; 192] {
        prf.sha256_key_states()
    }

    fn pbkdf2_iterate(key: &[u8; 192], u: &[u8; 32], n: u32, t: &mut [u8; 32]) {
        let mut scratch = [0u64; 48];
        // SAFETY: `key` is valid for reads of 192 bytes, `u` for reads of 32
        // bytes, `t` for reads and writes of 32 bytes and `scratch` for reads
        // and writes of 384 bytes; `t` and `scratch` are distinct objects
        // from each other and the others (`key` and `u` are only read), so
        // they do not overlap each other, the stack arguments (on ARMv7) or
        // (on x86-64) the return address and the stack below it. `key` holds
        // the streaming states for `K₀ ⊕ ipad` and `K₀ ⊕ opad` that
        // `vg_hmac_sha256_init` left.
        unsafe { vg_pbkdf2_hmac_sha256_iterate(key, u, n, t, &mut scratch) };
    }
}

/// Makes each hash function a [`Pbkdf2Hash`] with its verified
/// `vg_pbkdf2_hmac_<hash>_iterate`, given its streaming state size, its
/// working space (in 64-bit words) and its digest size.
#[cfg(target_arch = "x86_64")]
macro_rules! streaming_pbkdf2 {
    ($($hash:ident: $iterate:path, state: $state:literal, scratch: $scratch:literal, output: $output:literal;)*) => {$(
        impl Pbkdf2Hash for $hash {
            type Key = [u8; 2 * $state];

            fn pbkdf2_key(prf: &Hmac<Self>) -> [u8; 2 * $state] {
                let (inner, count) = prf.state().inner.state();
                debug_assert_eq!(count, Self::BLOCK_SIZE as u64);
                let mut key = [0; 2 * $state];
                key[..$state].copy_from_slice(&inner);
                key[$state..].copy_from_slice(&prf.state().outer);
                key
            }

            fn pbkdf2_iterate(key: &[u8; 2 * $state], u: &[u8; $output], n: u32, t: &mut [u8; $output]) {
                let mut scratch = [0u64; $scratch];
                // SAFETY: `key` is valid for reads of both streaming states,
                // `u` for reads of a digest, `t` for reads and writes of one
                // and `scratch` for reads and writes of its size; `t` and
                // `scratch` are distinct objects from each other and the
                // others (`key` and `u` are only read), so none of them
                // overlaps another written one or the call's stack frame.
                // `key` holds the streaming states for `K₀ ⊕ ipad` and
                // `K₀ ⊕ opad` that the hash's HMAC `init` left.
                unsafe { $iterate(key, u, n, t, &mut scratch) };
            }
        }
    )*};
}

#[cfg(target_arch = "x86_64")]
streaming_pbkdf2! {
    Sha1: vg_pbkdf2_hmac_sha1_iterate, state: 84, scratch: 56, output: 20;
    Md5: vg_pbkdf2_hmac_md5_iterate, state: 80, scratch: 48, output: 16;
    Sha384: vg_pbkdf2_hmac_sha384_iterate, state: 192, scratch: 96, output: 48;
    Sha512: vg_pbkdf2_hmac_sha512_iterate, state: 192, scratch: 96, output: 64;
    Sha512_224: vg_pbkdf2_hmac_sha512_224_iterate, state: 192, scratch: 96, output: 28;
    Sha512_256: vg_pbkdf2_hmac_sha512_256_iterate, state: 192, scratch: 96, output: 32;
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

/// Fills `out` with the key derived from `password` and `salt` with
/// `iterations` iterations of PBKDF2 with HMAC-SHA-256.
///
/// # Panics
///
/// If `out` is longer than (2³² − 1) · 32 bytes ("derived key too long" in
/// RFC 8018).
pub fn pbkdf2_hmac_sha256(password: &[u8], salt: &[u8], iterations: NonZeroU32, out: &mut [u8]) {
    pbkdf2_hmac::<Sha256>(password, salt, iterations, out);
}
