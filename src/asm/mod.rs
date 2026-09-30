// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Formally verified assembly, emitted from Lean. See `lean/README.md`.
//!
//! Every function in these modules is the direct rendering of an `Artifact`
//! whose machine code has been proven correct, memory safe and constant time
//! against its contract.

#[cfg(all(target_arch = "aarch64", target_endian = "little", target_pointer_width = "64", target_feature = "neon"))]
#[rustfmt::skip]
pub(crate) mod aarch64;

#[cfg(all(target_arch = "arm", target_endian = "little", not(target_vendor = "apple")))]
#[rustfmt::skip]
pub(crate) mod arm;

#[cfg(all(target_arch = "x86", target_feature = "sse2"))]
#[rustfmt::skip]
pub(crate) mod x86;

#[cfg(all(target_arch = "x86_64", target_pointer_width = "64", target_feature = "sse2"))]
#[rustfmt::skip]
pub(crate) mod x86_64;
