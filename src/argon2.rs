//! Argon2 version 1.3 (RFC 9106).
//!
//! The complete derivation is verified assembly (`VG.Spec.Argon2.deriveContract`),
//! including H₀, memory initialization, every filling pass and final H′. Hashing
//! follows the selected BLAKE2b backend. Rust only validates arguments, checks
//! the memory limit and allocates the matrix and scratch (and, for
//! [`verify`] and [`verify_keyed`], compares the derived key with the
//! expected one).
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
/// [`derive()`], [`derive_keyed`], [`verify`] and [`verify_keyed`] validate
/// them.
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

/// Why [`derive()`] or [`derive_keyed`] refused to derive a key, or [`verify`]
/// or [`verify_keyed`] to accept one.
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
    /// [`verify`] or [`verify_keyed`] derived a key other than the expected
    /// one: the password (or another input or a cost) is not the one it was
    /// derived from.
    KeyMismatch,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidParameters => "invalid Argon2 parameters",
            Self::MemoryLimitExceeded => "Argon2 would need more than the memory limit",
            Self::AllocationFailed => "could not allocate Argon2's memory",
            Self::KeyMismatch => "Argon2 derived key does not match",
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
    let inputs = Inputs {
        password,
        salt,
        secret,
        associated_data,
    };
    Derivation::new(params, inputs, max_memory, out.len())?.run(out);
    Ok(())
}

/// Checks a password against a stored derived key: [`verify_keyed`] with an
/// empty secret and associated data.
///
/// # Errors
///
/// As [`verify_keyed`].
pub fn verify(
    params: &Params,
    password: &[u8],
    salt: &[u8],
    max_memory: usize,
    expected: &[u8],
) -> Result<(), Error> {
    verify_keyed(params, password, salt, b"", b"", max_memory, expected)
}

/// Checks a password against a stored derived key: derives a key of
/// `expected.len()` bytes from `password`, `salt`, `secret` and
/// `associated_data` with the costs `params` (as [`derive_keyed`] does), if
/// that needs at most `max_memory` bytes, and compares it with `expected`.
///
/// The comparison is constant time: the time taken does not depend on
/// where, or whether, the keys differ. The derivation is
/// [`derive_keyed`]'s: Argon2i's leaks no input contents, while Argon2d's
/// and Argon2id's memory accesses depend on the password (see the module's
/// documentation). `expected.len()` is public (it decides how much is
/// derived). The derived key is wiped before returning.
///
/// The memory limit counts what [`derive_keyed`] needs, not the
/// `expected.len()` bytes allocated for the derived key.
///
/// # Errors
///
/// [`Error::KeyMismatch`] if the derived key is not `expected`; otherwise
/// as [`derive_keyed`], with `expected` in place of `out`: in particular
/// [`Error::InvalidParameters`] if `expected` is shorter than 4 bytes.
pub fn verify_keyed(
    params: &Params,
    password: &[u8],
    salt: &[u8],
    secret: &[u8],
    associated_data: &[u8],
    max_memory: usize,
    expected: &[u8],
) -> Result<(), Error> {
    let inputs = Inputs {
        password,
        salt,
        secret,
        associated_data,
    };
    let mut derivation = Derivation::new(params, inputs, max_memory, expected.len())?;
    let mut key = allocate(expected.len(), 0u8)?;
    derivation.run(&mut key);
    let matches = crate::ct::eq(&key, expected);
    crate::zeroize::zeroize(&mut key);
    if matches {
        Ok(())
    } else {
        Err(Error::KeyMismatch)
    }
}

/// The inputs of a derivation other than its costs.
#[derive(Clone, Copy)]
struct Inputs<'a> {
    password: &'a [u8],
    salt: &'a [u8],
    secret: &'a [u8],
    associated_data: &'a [u8],
}

/// A derivation whose costs and lengths [`Derivation::new`] checked, with
/// the memory Argon2 works in.
struct Derivation<'a> {
    /// The costs.
    params: Params,
    /// The other inputs.
    inputs: Inputs<'a>,
    /// The memory matrix, of `1024 · blocks` bytes.
    matrix: Vec<[u64; 128]>,
    /// 16 KiB of working space.
    scratch: Vec<[u64; 2048]>,
    /// The length of the key to derive.
    len: usize,
}

impl<'a> Derivation<'a> {
    /// The derivation of a key of `len` bytes from `inputs` with the costs
    /// `params`, if they and the lengths are valid and the matrix is at most
    /// `max_memory` bytes.
    fn new(
        params: &Params,
        inputs: Inputs<'a>,
        max_memory: usize,
        len: usize,
    ) -> Result<Self, Error> {
        let &Params {
            iterations,
            memory_kib,
            lanes,
            ..
        } = params;
        if !valid(
            iterations,
            memory_kib,
            lanes,
            [
                inputs.password.len(),
                inputs.salt.len(),
                inputs.secret.len(),
                inputs.associated_data.len(),
                len,
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
        Ok(Derivation {
            params: *params,
            inputs,
            matrix: allocate(blocks, [0; 128])?,
            scratch: allocate(1, [0; 2048])?,
            len,
        })
    }

    /// Fills `out`, of the length checked, with the key.
    fn run(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), self.len);
        let Params {
            variant,
            iterations,
            memory_kib,
            lanes,
        } = self.params;
        let Inputs {
            password,
            salt,
            secret,
            associated_data,
        } = self.inputs;
        let derive = match Blake2bBackend::select(crate::cpu::detected()) {
            Blake2bBackend::Scalar => vg_argon2,
        };
        // SAFETY: `Derivation::new` validated the costs and the lengths of
        // the inputs and `out`, which establishes every numeric precondition
        // of `deriveContract`, and `threads` is 1, in its range 1..2²⁴. The
        // matrix contains exactly the rounded block count and scratch is
        // 2048 u64s. Input slices are valid for their lengths; output and
        // both allocations are distinct mutable objects. They do not overlap
        // each other, any input, the caller's stack arguments or the
        // 344-byte assembly stack frame, and no region wraps the address
        // space. The selected BLAKE2b backend supplies every required CPU
        // feature.
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
                // derives the same key. The lanes are computed serially, by
                // one.
                1,
                secret.as_ptr(),
                secret.len(),
                associated_data.as_ptr(),
                associated_data.len(),
                self.matrix.as_mut_ptr(),
                self.matrix.len(),
                self.scratch.as_mut_ptr(),
                out.as_mut_ptr(),
                out.len(),
            )
        };
    }
}

fn valid(iterations: u32, memory_kib: u32, lanes: u32, lengths: [usize; 5]) -> bool {
    iterations > 0
        && (1..1 << 24).contains(&lanes)
        && memory_kib >= 8 * lanes
        && lengths[4] >= 4
        && lengths.into_iter().all(|n| n <= u32::MAX as usize)
}

/// A vector of `len` copies of `zero`, or `AllocationFailed`.
fn allocate<T: Clone>(len: usize, zero: T) -> Result<Vec<T>, Error> {
    let mut v = Vec::new();
    v.try_reserve_exact(len)
        .map_err(|_| Error::AllocationFailed)?;
    v.resize(len, zero);
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
        assert_eq!(
            allocate(usize::MAX, [0u64; 128]),
            Err(Error::AllocationFailed)
        );
    }
}
