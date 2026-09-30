//! ML-DSA-65: the tests of `mldsa.rs`.

#![cfg(target_arch = "x86_64")]

crate::mldsa::mldsa_tests!("65", mldsa65, SigningKey65, VerifyingKey65);
