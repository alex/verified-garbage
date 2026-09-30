//! ML-DSA-87 (FIPS 204): the tests of `mldsa.rs`.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

crate::mldsa::mldsa_tests!("ML-DSA-87", mldsa87, SigningKey87, VerifyingKey87);
