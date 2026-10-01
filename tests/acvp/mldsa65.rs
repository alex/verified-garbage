//! ML-DSA-65 (FIPS 204): the tests of `mldsa.rs`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

crate::mldsa::mldsa_tests!("ML-DSA-65", mldsa65, SigningKey65, VerifyingKey65);
