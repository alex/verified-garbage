//! ML-DSA-65 (FIPS 204), the module-lattice-based digital signature
//! algorithm, at security category 3.
//!
//! Key generation is the verified assembly function `vg_mldsa65_keygen`
//! (contract `VG.Spec.MlDsa.keyGenContract` for `mlDsa65`),
//! `ML-DSA.KeyGen_internal` (FIPS 204 Algorithm 6); signing and verification
//! are `vg_mldsa65_sign_message` and `vg_mldsa65_verify_message`
//! (`signMessageContract` and `verifyMessageContract`), `ML-DSA.Sign` and
//! `ML-DSA.Verify` (Algorithms 2 and 3), which format the message with its
//! context string, compute the message representative `μ` and call the
//! internal algorithms on it, `vg_mldsa65_sign` and `vg_mldsa65_verify`
//! (§6), all composing the verified polynomial arithmetic and SHA-3. This
//! module supplies the randomness and working space, and destroys the
//! intermediate values (§3.6.3).
//!
//! A private key is kept as the 32-byte seed `ξ` it is generated from
//! (§3.6.3), which [`SigningKey65::from_seed`] expands; the caller generates
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
    name: "ML-DSA-65",
    signing_key: SigningKey65,
    verifying_key: VerifyingKey65,
    keygen: crate::arch::mldsa65::vg_mldsa65_keygen,
    sign: crate::arch::mldsa65::vg_mldsa65_sign,
    verify: crate::arch::mldsa65::vg_mldsa65_verify,
    sign_message: crate::arch::mldsa65::vg_mldsa65_sign_message,
    verify_message: crate::arch::mldsa65::vg_mldsa65_verify_message,
    keygen_sha3: (crate::arch::mldsa65::vg_mldsa65_keygen_sha3, crate::arch::mldsa65::VG_MLDSA65_KEYGEN_SHA3_FEATURES),
    sign_sha3: (crate::arch::mldsa65::vg_mldsa65_sign_sha3, crate::arch::mldsa65::VG_MLDSA65_SIGN_SHA3_FEATURES),
    verify_sha3: (crate::arch::mldsa65::vg_mldsa65_verify_sha3, crate::arch::mldsa65::VG_MLDSA65_VERIFY_SHA3_FEATURES),
    sign_message_sha3: (crate::arch::mldsa65::vg_mldsa65_sign_message_sha3, crate::arch::mldsa65::VG_MLDSA65_SIGN_MESSAGE_SHA3_FEATURES),
    verify_message_sha3: (crate::arch::mldsa65::vg_mldsa65_verify_message_sha3, crate::arch::mldsa65::VG_MLDSA65_VERIFY_MESSAGE_SHA3_FEATURES),
    keygen_avx2: (crate::arch::mldsa65::vg_mldsa65_keygen_avx2, crate::arch::mldsa65::VG_MLDSA65_KEYGEN_AVX2_FEATURES),
    sign_avx2: (crate::arch::mldsa65::vg_mldsa65_sign_avx2, crate::arch::mldsa65::VG_MLDSA65_SIGN_AVX2_FEATURES),
    verify_avx2: (crate::arch::mldsa65::vg_mldsa65_verify_avx2, crate::arch::mldsa65::VG_MLDSA65_VERIFY_AVX2_FEATURES),
    sign_message_avx2: (crate::arch::mldsa65::vg_mldsa65_sign_message_avx2, crate::arch::mldsa65::VG_MLDSA65_SIGN_MESSAGE_AVX2_FEATURES),
    verify_message_avx2: (crate::arch::mldsa65::vg_mldsa65_verify_message_avx2, crate::arch::mldsa65::VG_MLDSA65_VERIFY_MESSAGE_AVX2_FEATURES),
    pk: 1952,
    sk: 4032,
    sig: 3309,
    scratch: 12928,
    message_scratch: 13056,
}
