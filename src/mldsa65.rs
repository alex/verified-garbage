//! ML-DSA-65 (FIPS 204), the module-lattice-based digital signature
//! algorithm, at security category 3.
//!
//! Key generation, signing and verification are the verified assembly
//! functions `vg_mldsa65_keygen`, `vg_mldsa65_sign` and `vg_mldsa65_verify`
//! (contracts `VG.Spec.MlDsa.keyGenContract`, `signContract` and
//! `verifyContract` for `mlDsa65`): FIPS 204's internal algorithms
//! `ML-DSA.KeyGen_internal`, `ML-DSA.Sign_internal` and
//! `ML-DSA.Verify_internal` (§6), with the message representative `μ` given,
//! which compose the verified polynomial arithmetic and SHA-3. This module
//! computes `μ` from the message and its context string with the verified
//! SHAKE256 (Algorithms 2 and 3), supplies the randomness and working space,
//! and destroys the intermediate values (§3.6.3).
//!
//! A private key is kept as the 32-byte seed `ξ` it is generated from
//! (§3.6.3), which [`SigningKey65::from_seed`] expands; the caller generates
//! the seed with an approved RBG. The expanded private key is never
//! exposed. HashML-DSA (§5.4) is not provided.
//!
//! The loops FIPS 204 lets an implementation bound (Appendix C) reach their
//! bounds with probability about 2⁻²⁵⁶ or less; the operation then fails
//! with [`Error::LoopBound`].

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

crate::mldsa_common::ml_dsa! {
    name: "ML-DSA-65",
    signing_key: SigningKey65,
    verifying_key: VerifyingKey65,
    keygen: crate::arch::mldsa65::vg_mldsa65_keygen,
    sign: crate::arch::mldsa65::vg_mldsa65_sign,
    verify: crate::arch::mldsa65::vg_mldsa65_verify,
    pk: 1952,
    sk: 4032,
    sig: 3309,
    scratch: 12928,
}
