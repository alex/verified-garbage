//! ML-DSA-44 (FIPS 204): the tests of `mldsa.rs`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

crate::mldsa::mldsa_tests!("ML-DSA-44", mldsa44, SigningKey44, VerifyingKey44);
