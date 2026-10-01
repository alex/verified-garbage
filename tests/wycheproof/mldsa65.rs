//! ML-DSA-65: the tests of `mldsa.rs`.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

crate::mldsa::mldsa_tests!("65", mldsa65, SigningKey65, VerifyingKey65);
