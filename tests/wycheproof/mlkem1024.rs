//! ML-KEM-1024: the tests of `mlkem.rs`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

crate::mlkem::mlkem_tests!(
    "1024",
    verified_garbage::mlkem1024,
    DecapsulationKey1024,
    EncapsulationKey1024
);
