//! Argon2 version 1.3 (RFC 9106).
//!
//! The complete derivation is verified assembly (`VG.Spec.Argon2.deriveContract`),
//! including H₀, memory initialization, every filling pass and final H′. Hashing
//! follows the selected BLAKE2b backend. Rust only validates arguments, checks
//! the memory limit and allocates the matrix and scratch.
//!
//! The costs are the named fields of [`Params`], so that none can be passed
//! in another's place. Lanes are evaluated serially: [`Params::lanes`] is the
//! algorithm's parallelism input `p`, which changes the key, not a number of
//! threads.
//!
//! Argon2i leaks no input contents. Argon2d and Argon2id permit the
//! data-dependent reference indices specified by `VG.Spec.Argon2.references`.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use alloc::vec::Vec;
use core::fmt;

use crate::arch::argon2::vg_argon2;
use crate::hashes::blake2b::Blake2bBackend;

/// Argon2's addressing variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Variant {
    /// Data-dependent addressing.
    Argon2d = 0,
    /// Data-independent addressing.
    Argon2i = 1,
    /// Independent addressing for the first half of the first pass.
    Argon2id = 2,
}

/// Argon2's cost parameters (RFC 9106 §3.1).
///
/// [`derive`] and [`derive_keyed`] validate them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    /// y: the addressing variant.
    pub variant: Variant,
    /// t: the number of passes over memory.
    pub iterations: u32,
    /// m: the memory size, in KiB.
    pub memory_kib: u32,
    /// p: the number of lanes (degree of parallelism; computed serially here).
    pub lanes: u32,
}

/// Why [`derive`] or [`derive_keyed`] refused to derive a key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// Invalid costs or lengths: iterations must be positive; lanes must be
    /// in 1..2²⁴; memory must be at least eight KiB per lane; inputs must be
    /// shorter than 2³² bytes and output must be 4..2³² bytes.
    InvalidParameters,
    /// The memory matrix, `1024 · blocks` bytes, exceeds `max_memory` (or the
    /// address space).
    MemoryLimitExceeded,
    /// Allocating the memory matrix or scratch failed.
    AllocationFailed,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidParameters => "invalid Argon2 parameters",
            Self::MemoryLimitExceeded => "Argon2 would need more than the memory limit",
            Self::AllocationFailed => "could not allocate Argon2's memory",
        })
    }
}

impl core::error::Error for Error {}

/// Fills `out` with the Argon2 version 1.3 key derived from `password` and
/// `salt` with the costs `params`, if that needs at most `max_memory` bytes:
/// [`derive_keyed`] with an empty secret and associated data.
///
/// # Errors
///
/// As [`derive_keyed`]; `out` is unchanged then.
pub fn derive(
    params: &Params,
    password: &[u8],
    salt: &[u8],
    max_memory: usize,
    out: &mut [u8],
) -> Result<(), Error> {
    derive_keyed(params, password, salt, b"", b"", max_memory, out)
}

/// Fills `out` with the Argon2 version 1.3 key derived from `password`,
/// `salt`, the secret value `secret` (K) and `associated_data` (X) with the
/// costs `params`, if that needs at most `max_memory` bytes. `secret` and
/// `associated_data` may be empty.
///
/// Argon2 needs `1024 · blocks` bytes for its memory matrix, where `blocks`
/// is `params.memory_kib` rounded down to a multiple of `4 · params.lanes`.
/// It also needs 16 KiB of working space, which (like the stack) the limit
/// does not count.
///
/// # Errors
///
/// [`Error::InvalidParameters`] if `params` or a length is not valid,
/// [`Error::MemoryLimitExceeded`] if the memory matrix would need more than
/// `max_memory` bytes, and [`Error::AllocationFailed`] if allocating the
/// matrix or the working space fails. `out` is unchanged then.
pub fn derive_keyed(
    params: &Params,
    password: &[u8],
    salt: &[u8],
    secret: &[u8],
    associated_data: &[u8],
    max_memory: usize,
    out: &mut [u8],
) -> Result<(), Error> {
    let &Params {
        variant,
        iterations,
        memory_kib,
        lanes,
    } = params;
    if !valid(
        iterations,
        memory_kib,
        lanes,
        [
            password.len(),
            salt.len(),
            secret.len(),
            associated_data.len(),
            out.len(),
        ],
    ) {
        return Err(Error::InvalidParameters);
    }
    let divisor = 4 * lanes;
    let blocks = (memory_kib / divisor * divisor) as usize;
    if blocks
        .checked_mul(1024)
        .is_none_or(|bytes| bytes > max_memory)
    {
        return Err(Error::MemoryLimitExceeded);
    }
    let mut matrix = allocate::<128>(blocks)?;
    let mut scratch = allocate::<2048>(1)?;
    let derive = match Blake2bBackend::select(crate::cpu::detected()) {
        Blake2bBackend::Scalar => vg_argon2,
    };
    // SAFETY: validation establishes every numeric precondition of
    // `deriveContract`, and `threads` is 1, in its range 1..2²⁴. The matrix
    // contains exactly the rounded block count and scratch is 2048 u64s.
    // Input slices are valid for their lengths; output and both allocations
    // are distinct mutable objects. They do not overlap each other, any
    // input, the caller's stack arguments or the 344-byte assembly stack
    // frame, and no region wraps the address space. The selected BLAKE2b
    // backend supplies every required CPU feature.
    unsafe {
        derive(
            variant as u32,
            password.as_ptr(),
            password.len(),
            salt.as_ptr(),
            salt.len(),
            iterations,
            memory_kib,
            lanes,
            // `threads`, a maximum worker count: `deriveContract`'s
            // postcondition does not depend on it, so every valid value
            // derives the same key. The lanes are computed serially, by one.
            1,
            secret.as_ptr(),
            secret.len(),
            associated_data.as_ptr(),
            associated_data.len(),
            matrix.as_mut_ptr(),
            blocks,
            scratch.as_mut_ptr(),
            out.as_mut_ptr(),
            out.len(),
        )
    };
    Ok(())
}

fn valid(iterations: u32, memory_kib: u32, lanes: u32, lengths: [usize; 5]) -> bool {
    iterations > 0
        && (1..1 << 24).contains(&lanes)
        && memory_kib >= 8 * lanes
        && lengths[4] >= 4
        && lengths.into_iter().all(|n| n <= u32::MAX as usize)
}

fn allocate<const N: usize>(len: usize) -> Result<Vec<[u64; N]>, Error> {
    let mut v = Vec::new();
    v.try_reserve_exact(len)
        .map_err(|_| Error::AllocationFailed)?;
    v.resize(len, [0; N]);
    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn length_limits() {
        assert!(valid(1, 8, 1, [u32::MAX as usize; 5]));
        for j in 0..5 {
            let mut lengths = [0, 0, 0, 0, 4];
            lengths[j] = u32::MAX as usize + 1;
            assert!(!valid(1, 8, 1, lengths));
        }
    }

    #[test]
    fn allocation_failure() {
        assert_eq!(allocate::<128>(usize::MAX), Err(Error::AllocationFailed));
    }
}
