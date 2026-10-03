//! ML-KEM-768 (FIPS 203), the module-lattice-based key-encapsulation
//! mechanism, at security category 3.
//!
//! Key generation, encapsulation and decapsulation are the verified
//! assembly functions `vg_mlkem768_keygen`, `vg_mlkem768_encaps` and
//! `vg_mlkem768_decaps` (contracts `VG.Spec.MlKem.keyGenContract`,
//! `encapsContract` and `decapsContract`): FIPS 203's internal algorithms
//! `ML-KEM.KeyGen_internal`, `ML-KEM.Encaps_internal` and
//! `ML-KEM.Decaps_internal` (§6), which compose the verified polynomial
//! arithmetic and SHA-3. The encapsulation key check of §7.2 is
//! `vg_mlkem768_check_ek`. This module supplies their randomness and working
//! space, and destroys the intermediate values (§3.3).
//!
//! A decapsulation key is kept as the 64-byte seed `d ‖ z` it is generated
//! from (§3.3), which [`DecapsulationKey768::from_seed`] expands; the caller
//! generates the seed with an approved RBG. The expanded decapsulation key is
//! never exposed, so the decapsulation keys this module uses pass the checks
//! of §7.3 by construction. An encapsulation key from elsewhere passes the
//! check of §7.2 in [`EncapsulationKey768::from_bytes`].
//!
//! The bound on `SampleNTT`'s loop (280 iterations, as Appendix B allows) is
//! reached with probability less than 2⁻²⁶¹ for each call; key generation,
//! encapsulation and decapsulation each call it 9 times (once for each
//! entry of the matrix `Â`), so an operation reaches it with probability
//! less than 2⁻²⁵⁸, and then fails with [`Error::SampleBound`].
//!
//! On x86-64, key generation, encapsulation and decapsulation have an
//! instance for each implementation of `vg_mlkem_sample_ntt4`, which samples
//! four entries of the matrix at once, and each operation calls the best one
//! the CPU can run.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

crate::mlkem_common::ml_kem! {
    name: "ML-KEM-768",
    encapsulation_key: EncapsulationKey768,
    decapsulation_key: DecapsulationKey768,
    check_ek: crate::arch::mlkem768::vg_mlkem768_check_ek,
    keygen: crate::arch::mlkem768::vg_mlkem768_keygen,
    encaps: crate::arch::mlkem768::vg_mlkem768_encaps,
    decaps: crate::arch::mlkem768::vg_mlkem768_decaps,
    keygen_sha3: (crate::arch::mlkem768::vg_mlkem768_keygen_sha3, crate::arch::mlkem768::VG_MLKEM768_KEYGEN_SHA3_FEATURES),
    encaps_sha3: (crate::arch::mlkem768::vg_mlkem768_encaps_sha3, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_SHA3_FEATURES),
    decaps_sha3: (crate::arch::mlkem768::vg_mlkem768_decaps_sha3, crate::arch::mlkem768::VG_MLKEM768_DECAPS_SHA3_FEATURES),
    keygen_avx2: (crate::arch::mlkem768::vg_mlkem768_keygen_avx2, crate::arch::mlkem768::VG_MLKEM768_KEYGEN_AVX2_FEATURES),
    encaps_avx2: (crate::arch::mlkem768::vg_mlkem768_encaps_avx2, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_AVX2_FEATURES),
    decaps_avx2: (crate::arch::mlkem768::vg_mlkem768_decaps_avx2, crate::arch::mlkem768::VG_MLKEM768_DECAPS_AVX2_FEATURES),
    ek: 1184,
    dk: 2400,
    ct: 1088,
    scratch: 4096,
}
