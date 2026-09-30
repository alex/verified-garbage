//! ML-DSA-65 (FIPS 204): the tests of `mldsa.rs`.

#![cfg(target_arch = "x86_64")]

crate::mldsa::mldsa_tests!("ML-DSA-65", mldsa65, SigningKey65, VerifyingKey65);
