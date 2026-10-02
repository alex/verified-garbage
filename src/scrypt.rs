//! scrypt (RFC 7914 §6).
//!
//! The whole derivation is the verified `vg_scrypt` (contract
//! `VG.Spec.Scrypt.scryptContract`): it calls the verified
//! `vg_pbkdf2_hmac_sha256` for `B = PBKDF2-HMAC-SHA256 (P, S, 1, p · 128 · r)`
//! and for the derived key `PBKDF2-HMAC-SHA256 (P, B, 1, dkLen)`, and in
//! between the verified `vg_scrypt_romix` on each of the `p` blocks of `B`.
//! It follows the implementation of SHA-256 that `Sha256` runs on this CPU:
//! on x86-64 and x86, `vg_scrypt_shani` with the SHA extensions, the same
//! verified code calling `vg_pbkdf2_hmac_sha256_shani`, with the same
//! contract; likewise `vg_scrypt_avx2` with AVX2 on x86-64, and on AArch64
//! `vg_scrypt_sha2` with the SHA-256 instructions.
//!
//! ROMix (contract `VG.Spec.Scrypt.roMixContract`) calls the verified
//! `vg_scrypt_blockmix` and `vg_salsa20_8`. This module only checks the
//! parameters and allocates the memory scrypt works in (and, for [`verify`],
//! compares the derived key with the expected one).
//!
//! scryptROMix reads its table `V` at indices derived from the password, so
//! its memory accesses (and hence its timing, through the caches) depend on
//! them. That is inherent to scrypt; the contracts declare that scrypt leaks
//! these indices and nothing else secret.

#![cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86"
    ),
    feature = "alloc"
))]

use alloc::vec::Vec;
use core::fmt;

use crate::arch::scrypt::vg_scrypt;
#[cfg(target_arch = "x86_64")]
use crate::arch::scrypt::vg_scrypt_avx2;
#[cfg(target_arch = "aarch64")]
use crate::arch::scrypt::vg_scrypt_sha2;
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use crate::arch::scrypt::vg_scrypt_shani;
use crate::hashes::sha256::Sha256Backend;

/// Why [`scrypt`] refused to derive a key, or [`verify`] to accept one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The parameters are not valid (RFC 7914 §2 and §6): `n` must be a
    /// power of two greater than 1 and less than `2^(128 r / 8)`, `r` and
    /// `p` must be positive with `p ≤ (2³² − 1) · 32 / (128 r)`, and the
    /// derived key must be 1 to (2³² − 1) · 32 bytes long.
    InvalidParameters,
    /// The memory it needs, `128 · (r · (n + p) + r + 2)` bytes, exceeds
    /// `max_memory` (or the address space).
    MemoryLimitExceeded,
    /// Allocating that memory failed.
    AllocationFailed,
    /// [`verify`] derived a key other than the expected one: the password
    /// (or the salt or a parameter) is not the one it was derived from.
    KeyMismatch,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidParameters => "invalid scrypt parameters",
            Error::MemoryLimitExceeded => "scrypt would need more than the memory limit",
            Error::AllocationFailed => "could not allocate scrypt's memory",
            Error::KeyMismatch => "scrypt derived key does not match",
        })
    }
}

impl core::error::Error for Error {}

/// The 128-byte chunks of working space scrypt allocates beyond ROMix's
/// `r + 2`, so that PBKDF2-HMAC-SHA256's 1,600 bytes fit in the `r + 16`
/// chunks `vg_scrypt` takes.
const PBKDF2_CHUNKS: usize = 14;

/// A zeroed vector of `len` 128-byte chunks, or `AllocationFailed`.
fn chunks(len: usize) -> Result<Vec<[u8; 128]>, Error> {
    let mut v = Vec::new();
    v.try_reserve_exact(len)
        .map_err(|_| Error::AllocationFailed)?;
    v.resize(len, [0; 128]);
    Ok(v)
}

/// Fills `out` with the key derived from `password` and `salt` by scrypt
/// with CPU/memory cost parameter `n`, block size parameter `r` and
/// parallelization parameter `p`, if that needs at most `max_memory` bytes.
///
/// scrypt needs `128 · (r · (n + p) + r + 2)` bytes: `128 · r · n` for
/// ROMix's table, `128 · r · p` for the blocks and `128 · (r + 2)` of working
/// space. For `r ≥ 2` that is at most OpenSSL's `EVP_PBE_scrypt` accounting,
/// `128 · r · (n + p + 2)` bytes. The working space also holds PBKDF2's,
/// 1,792 bytes more, which (like the stack) the limit does not count.
///
/// # Errors
///
/// [`Error::InvalidParameters`] if the parameters or `out`'s length are not
/// valid, [`Error::MemoryLimitExceeded`] if scrypt would need more than
/// `max_memory` bytes, and [`Error::AllocationFailed`] if allocating them
/// fails. `out` is unchanged then.
pub fn scrypt(
    password: &[u8],
    salt: &[u8],
    n: u64,
    r: u32,
    p: u32,
    max_memory: usize,
    out: &mut [u8],
) -> Result<(), Error> {
    Memory::new(n, r, p, max_memory, out.len())?.derive(password, salt, out);
    Ok(())
}

/// Checks a password against a stored derived key: derives a key of `N`
/// bytes from `password` and `salt` by scrypt with parameters `n`, `r` and
/// `p` (as [`scrypt`] does), if that needs at most `max_memory` bytes, and
/// compares it with `expected`.
///
/// The comparison is constant time: the time taken does not depend on
/// where, or whether, the keys differ. The derivation is [`scrypt`]'s, whose
/// memory accesses depend on the password (see the module's documentation).
/// `N` is public. The derived key is wiped before returning.
///
/// `N` is a type parameter, at least 16 (a smaller one is an error when the
/// call is compiled), so that the length checked is fixed in the caller's
/// code: scrypt's keys of different lengths share their prefixes, so a key
/// checked at a length taken from a slice (a truncated stored key, or one an
/// attacker sent) would match a password on as few bytes as it has. A caller
/// with the stored key in a slice converts it (`stored.try_into()`), which
/// fails if it does not have the length the code expects.
///
/// # Errors
///
/// [`Error::KeyMismatch`] if the derived key is not `expected`; otherwise
/// as [`scrypt`], with `expected` in place of `out`.
pub fn verify<const N: usize>(
    password: &[u8],
    salt: &[u8],
    n: u64,
    r: u32,
    p: u32,
    max_memory: usize,
    expected: &[u8; N],
) -> Result<(), Error> {
    crate::ct::assert_verify_len!(N);
    let mut memory = Memory::new(n, r, p, max_memory, N)?;
    let mut key = [0u8; N];
    memory.derive(password, salt, &mut key);
    let matches = crate::ct::eq(&key, expected);
    crate::zeroize::zeroize(&mut key);
    if matches {
        Ok(())
    } else {
        Err(Error::KeyMismatch)
    }
}

/// The memory scrypt works in, for parameters [`Memory::new`] checked.
struct Memory {
    /// The block size parameter `r`.
    r: usize,
    /// The `p` blocks of `128 r` bytes.
    b: Vec<[u8; 128]>,
    /// ROMix's table, of `n` blocks.
    v: Vec<[u8; 128]>,
    /// `r + 16` chunks of working space.
    scratch: Vec<[u8; 128]>,
    /// The length of the key to derive.
    len: usize,
}

impl Memory {
    /// The memory to derive a key of `len` bytes with parameters `n`, `r`
    /// and `p` in, if they are valid and it is at most `max_memory` bytes.
    fn new(n: u64, r: u32, p: u32, max_memory: usize, len: usize) -> Result<Memory, Error> {
        // RFC 7914 §2 and §6, as `VG.Spec.Scrypt.valid` states them.
        let (n64, r64, p64) = (n, u64::from(r), u64::from(p));
        let max_len = (u64::from(u32::MAX)) * 32;
        let n_ok = n64 > 1 && n64.is_power_of_two() && (r64 * 16 >= 64 || n64 < 1 << (r64 * 16));
        let p_ok = r64 > 0 && p64 > 0 && p64 <= max_len / (128 * r64);
        let len_ok = len != 0 && (len as u64) <= max_len;
        if !(n_ok && p_ok && len_ok) {
            return Err(Error::InvalidParameters);
        }
        // `128 (r (n + p) + r + 2)` bytes, in chunks of 128.
        let size = |n: u64| usize::try_from(n).ok();
        let (n, r, p) = (size(n64), r as usize, p as usize);
        let vlen = n.and_then(|n| n.checked_mul(r));
        let total = vlen.and_then(|v| v.checked_add(r * p)?.checked_add(r + 2)?.checked_mul(128));
        let (Some(vlen), Some(total)) = (vlen, total) else {
            return Err(Error::MemoryLimitExceeded);
        };
        if total > max_memory {
            return Err(Error::MemoryLimitExceeded);
        }
        Ok(Memory {
            r,
            b: chunks(r * p)?,
            v: chunks(vlen)?,
            scratch: chunks(r + 2 + PBKDF2_CHUNKS)?,
            len,
        })
    }

    /// Fills `out`, of the length the memory was allocated for, with the
    /// key derived from `password` and `salt`.
    fn derive(&mut self, password: &[u8], salt: &[u8], out: &mut [u8]) {
        assert_eq!(out.len(), self.len);
        let backend = Sha256Backend::select(crate::cpu::detected());
        derive(
            backend,
            password,
            salt,
            self.r,
            &mut self.b,
            &mut self.v,
            &mut self.scratch,
            out,
        );
    }
}

/// scrypt with block size parameter `r`, cost parameter `N = v.len() / r`
/// and parallelization parameter `p = b.len() / r`, for parameters that
/// [`Memory::new`] checked, with `r + 16` chunks of `scratch`, by the
/// implementation `backend` (which must have been selected for this CPU).
#[allow(clippy::too_many_arguments)]
fn derive(
    backend: Sha256Backend,
    password: &[u8],
    salt: &[u8],
    r: usize,
    b: &mut [[u8; 128]],
    v: &mut [[u8; 128]],
    scratch: &mut [[u8; 128]],
    out: &mut [u8],
) {
    let scrypt = match backend {
        Sha256Backend::Scalar => vg_scrypt,
        #[cfg(target_arch = "aarch64")]
        Sha256Backend::Sha2 => vg_scrypt_sha2,
        #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
        Sha256Backend::ShaNi => vg_scrypt_shani,
        #[cfg(target_arch = "x86_64")]
        Sha256Backend::Avx2 => vg_scrypt_avx2,
    };
    // SAFETY: `r > 0`; `b.len() = r p` and `v.len() = n r` for `n`, `r`, `p`
    // and `out.len()` that are valid (`Memory::new` checked them as
    // `VG.Spec.Scrypt.valid` states them, and `out.len() ≤ (2³² − 1) · 32`),
    // and `scratch.len() = r + 16`. `password` and `salt` are valid for
    // reads of their lengths, `b`, `v` and `scratch` for reads and writes of
    // 128 bytes per chunk and `out` of its length; `b`, `v`, `scratch` and
    // `out` are distinct objects from each other and the others (`password`
    // and `salt` are only read), so none of them overlaps another written
    // one or the call's stack frame, and, as Rust objects, none wraps around
    // the address space. `scrypt` needs no CPU feature that `backend`, the
    // implementation of SHA-256, was not selected for
    // (`tests::backend_features`).
    unsafe {
        scrypt(
            password.as_ptr(),
            password.len(),
            salt.as_ptr(),
            salt.len(),
            r,
            b.as_mut_ptr(),
            b.len(),
            v.as_mut_ptr(),
            v.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
            out.as_mut_ptr(),
            out.len(),
        )
    };
}

#[cfg(all(
    test,
    any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86")
))]
mod tests {
    use super::*;
    #[cfg(target_arch = "x86_64")]
    use crate::arch::scrypt::VG_SCRYPT_AVX2_FEATURES;
    #[cfg(target_arch = "aarch64")]
    use crate::arch::scrypt::VG_SCRYPT_SHA2_FEATURES;
    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    use crate::arch::scrypt::VG_SCRYPT_SHANI_FEATURES;
    use crate::cpu::{Features, NAMES};

    /// Each implementation of `vg_scrypt` needs no CPU feature that the
    /// implementation of SHA-256 is not selected for: on every set of
    /// features that selects it.
    #[test]
    fn backend_features() {
        #[cfg(target_arch = "x86_64")]
        let variants = [
            (Sha256Backend::ShaNi, VG_SCRYPT_SHANI_FEATURES),
            (Sha256Backend::Avx2, VG_SCRYPT_AVX2_FEATURES),
        ];
        #[cfg(target_arch = "x86")]
        let variants = [(Sha256Backend::ShaNi, VG_SCRYPT_SHANI_FEATURES)];
        #[cfg(target_arch = "aarch64")]
        let variants = [(Sha256Backend::Sha2, VG_SCRYPT_SHA2_FEATURES)];
        for (backend, req) in variants {
            for bits in 0..1u32 << NAMES.len() {
                let f = Features(bits);
                if Sha256Backend::select(f) == backend {
                    assert!(f.contains(Features::all(&[req])));
                }
            }
        }
    }
}

#[cfg(test)]
mod derive_tests {
    use super::*;

    /// The implementation selected for this CPU derives the same key as the
    /// baseline one (CI runs this on CPUs that select each of them).
    #[test]
    fn selected_matches_baseline() {
        let (n, r, p) = (16, 2, 2);
        let derive_with = |backend| {
            let mut b = chunks(r * p).unwrap();
            let mut v = chunks(n * r).unwrap();
            let mut scratch = chunks(r + 2 + PBKDF2_CHUNKS).unwrap();
            let mut out = [0u8; 80];
            derive(
                backend,
                b"password",
                b"salt",
                r,
                &mut b,
                &mut v,
                &mut scratch,
                &mut out,
            );
            out
        };
        let selected = Sha256Backend::select(crate::cpu::detected());
        assert_eq!(derive_with(selected), derive_with(Sha256Backend::Scalar));
        let mut out = [0u8; 80];
        scrypt(
            b"password",
            b"salt",
            n as u64,
            r as u32,
            p as u32,
            usize::MAX,
            &mut out,
        )
        .unwrap();
        assert_eq!(out, derive_with(selected));
    }
}
