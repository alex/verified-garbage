//! ML-KEM-1024: the benchmarks of `mlkem.rs`.

use criterion::Criterion;

pub const USES: &[&str] = &["mlkem1024", "mlkem_common", "mlkem", "sha3"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]
pub fn bench(c: &mut Criterion) {
    crate::mlkem::mlkem_bench!(
        c,
        verified_garbage::mlkem1024,
        DecapsulationKey1024,
        EncapsulationKey1024
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
)))]
pub fn bench(_: &mut Criterion) {}
