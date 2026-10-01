//! ML-DSA-87: the tests of `mldsa.rs`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

crate::mldsa::mldsa_tests!("87", mldsa87, SigningKey87, VerifyingKey87);
