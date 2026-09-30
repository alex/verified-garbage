//! ML-DSA-44 (FIPS 204): the tests of `mldsa.rs`.

#![cfg(target_arch = "x86_64")]

crate::mldsa::mldsa_tests!("ML-DSA-44", mldsa44, SigningKey44, VerifyingKey44);
