// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Formally verified assembly, emitted from Lean. See `lean/README.md`.
//!
//! Every function in these modules is the direct rendering of an `Artifact`
//! whose machine code has been proven correct, memory safe and constant time
//! against its contract.

#[cfg(all(target_arch = "aarch64", target_endian = "little", target_pointer_width = "64"))]
#[rustfmt::skip]
pub(crate) mod aarch64;

#[cfg(all(target_arch = "arm", target_endian = "little"))]
#[rustfmt::skip]
pub(crate) mod arm;

#[cfg(target_arch = "x86")]
#[rustfmt::skip]
pub(crate) mod x86;

#[cfg(all(target_arch = "x86_64", target_pointer_width = "64"))]
#[rustfmt::skip]
pub(crate) mod x86_64;
