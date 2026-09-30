//! ML-DSA-44: the tests of `mldsa.rs`.

#![cfg(target_arch = "x86_64")]

crate::mldsa::mldsa_tests!("44", mldsa44, SigningKey44, VerifyingKey44);
