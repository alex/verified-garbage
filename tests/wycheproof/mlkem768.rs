//! ML-KEM-768: the tests of `mlkem.rs`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

crate::mlkem::mlkem_tests!(
    "768",
    verified_garbage::mlkem768,
    DecapsulationKey768,
    EncapsulationKey768
);
