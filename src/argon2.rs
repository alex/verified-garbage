//! Argon2 version 1.3 (RFC 9106).
//!
//! The complete derivation is verified assembly (`VG.Spec.Argon2.deriveContract`),
//! including H₀, memory initialization, every filling pass and final H′. Hashing
//! follows the selected BLAKE2b backend. Rust only validates arguments and
//! allocates the matrix and scratch. Lanes are evaluated serially: `threads`
//! limits workers without changing the result.
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

/// Why [`derive`] refused to derive a key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// Invalid costs or lengths: iterations must be positive; lanes and
    /// threads must be in 1..2²⁴; memory must be at least eight KiB per lane;
    /// inputs must be shorter than 2³² bytes and output must be 4..2³² bytes.
    InvalidParameters,
    /// Allocating the memory matrix or scratch failed.
    AllocationFailed,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidParameters => "invalid Argon2 parameters",
            Self::AllocationFailed => "could not allocate Argon2's memory",
        })
    }
}

impl core::error::Error for Error {}

/// Fills `out` with an Argon2 version 1.3 key. `memory_cost` is in KiB and
/// `iterations` counts passes. `lanes` is the algorithm's parallelism input;
/// `threads` is a maximum worker count and does not change the key. `secret`
/// and `associated_data` may be empty. The matrix contains
/// `4 * lanes * floor(memory_cost / (4 * lanes))` blocks of 1024 bytes;
/// scratch occupies another 16 KiB.
///
/// # Errors
///
/// Returns [`Error::InvalidParameters`] for invalid costs or lengths and
/// [`Error::AllocationFailed`] if memory allocation fails. `out` is unchanged
/// on either error.
#[allow(clippy::too_many_arguments)]
pub fn derive(
    variant: Variant,
    password: &[u8],
    salt: &[u8],
    iterations: u32,
    memory_cost: u32,
    lanes: u32,
    threads: u32,
    secret: &[u8],
    associated_data: &[u8],
    out: &mut [u8],
) -> Result<(), Error> {
    if !valid(
        iterations,
        memory_cost,
        lanes,
        threads,
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
    let blocks = (memory_cost / divisor * divisor) as usize;
    let mut matrix = allocate::<128>(blocks)?;
    let mut scratch = allocate::<2048>(1)?;
    let derive = match Blake2bBackend::select(crate::cpu::detected()) {
        Blake2bBackend::Scalar => vg_argon2,
    };
    // SAFETY: validation establishes every numeric precondition of
    // `deriveContract`. The matrix contains exactly the rounded block count
    // and scratch is 2048 u64s. Input slices are valid for their lengths;
    // output and both allocations are distinct mutable objects. They do not
    // overlap each other, any input, the caller's stack arguments or the
    // 344-byte assembly stack frame, and no region wraps the address space.
    // The selected BLAKE2b backend supplies every required CPU feature.
    unsafe {
        derive(
            variant as u32,
            password.as_ptr(),
            password.len(),
            salt.as_ptr(),
            salt.len(),
            iterations,
            memory_cost,
            lanes,
            threads,
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

fn valid(iterations: u32, memory: u32, lanes: u32, threads: u32, lengths: [usize; 5]) -> bool {
    iterations > 0
        && (1..1 << 24).contains(&lanes)
        && (1..1 << 24).contains(&threads)
        && memory >= 8 * lanes
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
        assert!(valid(1, 8, 1, 1, [u32::MAX as usize; 5]));
        for j in 0..5 {
            let mut lengths = [0, 0, 0, 0, 4];
            lengths[j] = u32::MAX as usize + 1;
            assert!(!valid(1, 8, 1, 1, lengths));
        }
    }

    #[test]
    fn allocation_failure() {
        assert_eq!(allocate::<128>(usize::MAX), Err(Error::AllocationFailed));
    }
}
