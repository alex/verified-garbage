//! ML-DSA-87: the tests of `mldsa.rs`.

#![cfg(target_arch = "x86_64")]

crate::mldsa::mldsa_tests!("87", mldsa87, SigningKey87, VerifyingKey87);
