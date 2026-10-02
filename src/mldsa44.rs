//! ML-DSA-44 (FIPS 204), the module-lattice-based digital signature
//! algorithm, at security category 2.
//!
//! Key generation, signing and verification are the verified assembly
//! functions `vg_mldsa44_keygen`, `vg_mldsa44_sign` and `vg_mldsa44_verify`
//! (contracts `VG.Spec.MlDsa.keyGenContract`, `signContract` and
//! `verifyContract` for `mlDsa44`): FIPS 204's internal algorithms
//! `ML-DSA.KeyGen_internal`, `ML-DSA.Sign_internal` and
//! `ML-DSA.Verify_internal` (§6), with the message representative `μ` given,
//! which compose the verified polynomial arithmetic and SHA-3. This module
//! computes `μ` from the message and its context string with the verified
//! SHAKE256 (Algorithms 2 and 3), supplies the randomness and working space,
//! and destroys the intermediate values (§3.6.3).
//!
//! A private key is kept as the 32-byte seed `ξ` it is generated from
//! (§3.6.3), which [`SigningKey44::from_seed`] expands; the caller generates
//! the seed with an approved RBG. The expanded private key is never
//! exposed. HashML-DSA (§5.4) is not provided.
//!
//! The loops FIPS 204 lets an implementation bound (Appendix C) reach their
//! bounds with probability about 2⁻²⁵⁶ or less; the operation then fails
//! with [`Error::LoopBound`].

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

crate::mldsa_common::ml_dsa! {
    name: "ML-DSA-44",
    signing_key: SigningKey44,
    verifying_key: VerifyingKey44,
    keygen: crate::arch::mldsa44::vg_mldsa44_keygen,
    sign: crate::arch::mldsa44::vg_mldsa44_sign,
    verify: crate::arch::mldsa44::vg_mldsa44_verify,
    keygen_sha3: (crate::arch::mldsa44::vg_mldsa44_keygen_sha3, crate::arch::mldsa44::VG_MLDSA44_KEYGEN_SHA3_FEATURES),
    sign_sha3: (crate::arch::mldsa44::vg_mldsa44_sign_sha3, crate::arch::mldsa44::VG_MLDSA44_SIGN_SHA3_FEATURES),
    verify_sha3: (crate::arch::mldsa44::vg_mldsa44_verify_sha3, crate::arch::mldsa44::VG_MLDSA44_VERIFY_SHA3_FEATURES),
    keygen_avx2: (crate::arch::mldsa44::vg_mldsa44_keygen_avx2, crate::arch::mldsa44::VG_MLDSA44_KEYGEN_AVX2_FEATURES),
    sign_avx2: (crate::arch::mldsa44::vg_mldsa44_sign_avx2, crate::arch::mldsa44::VG_MLDSA44_SIGN_AVX2_FEATURES),
    verify_avx2: (crate::arch::mldsa44::vg_mldsa44_verify_avx2, crate::arch::mldsa44::VG_MLDSA44_VERIFY_AVX2_FEATURES),
    pk: 1312,
    sk: 2560,
    sig: 2420,
    scratch: 9728,
}
