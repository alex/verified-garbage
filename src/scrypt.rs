//! scrypt (RFC 7914 §6).
//!
//! `B = PBKDF2-HMAC-SHA256 (P, S, 1, p · 128 · r)` and the derived key
//! `PBKDF2-HMAC-SHA256 (P, B, 1, dkLen)` are [`pbkdf2_hmac_sha256`]. In
//! between, each of the `p` blocks of `B` goes through the verified
//! `vg_scrypt_romix` (contract `VG.Spec.Scrypt.roMixContract`), which calls
//! the verified `vg_scrypt_blockmix` and `vg_salsa20_8`. This module only
//! checks the parameters and allocates the memory ROMix works in.
//!
//! scryptROMix reads its table `V` at indices derived from the password, so
//! its memory accesses (and hence its timing, through the caches) depend on
//! them. That is inherent to scrypt; ROMix's contract declares that it leaks
//! these indices and nothing else secret.

use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroU32;

use crate::asm::x86_64::scrypt::vg_scrypt_romix;
use crate::pbkdf2::pbkdf2_hmac_sha256;

/// Why [`scrypt`] refused to derive a key.
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
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidParameters => "invalid scrypt parameters",
            Error::MemoryLimitExceeded => "scrypt would need more than the memory limit",
            Error::AllocationFailed => "could not allocate scrypt's memory",
        })
    }
}

impl core::error::Error for Error {}

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
/// `128 · r · (n + p + 2)` bytes.
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
    // RFC 7914 §2 and §6, as `VG.Spec.Scrypt.valid` states them.
    let (n64, r64, p64) = (n, u64::from(r), u64::from(p));
    let max_len = (u64::from(u32::MAX)) * 32;
    let n_ok = n64 > 1 && n64.is_power_of_two() && (r64 * 16 >= 64 || n64 < 1 << (r64 * 16));
    let p_ok = r64 > 0 && p64 > 0 && p64 <= max_len / (128 * r64);
    let len_ok = !out.is_empty() && (out.len() as u64) <= max_len;
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
    let mut b = chunks(r * p)?;
    let mut v = chunks(vlen)?;
    let mut scratch = chunks(r + 2)?;
    pbkdf2_hmac_sha256(password, salt, NonZeroU32::MIN, b.as_flattened_mut());
    for block in b.chunks_exact_mut(r) {
        // SAFETY: `block` is valid for reads and writes of `128 r` bytes,
        // `v` of `128 vlen` bytes and `scratch` of `128 (r + 2)` bytes; they
        // are distinct allocations, so they do not overlap each other or the
        // stack, and they do not wrap around the address space. `r > 0`,
        // `vlen = n r` with `n` a power of two, and `slen = r + 2`.
        unsafe {
            vg_scrypt_romix(
                block.as_mut_ptr(),
                r,
                v.as_mut_ptr(),
                vlen,
                scratch.as_mut_ptr(),
                r + 2,
            )
        };
    }
    pbkdf2_hmac_sha256(password, b.as_flattened(), NonZeroU32::MIN, out);
    Ok(())
}
