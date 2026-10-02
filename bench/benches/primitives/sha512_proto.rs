//! EXPERIMENT, NOT FOR MERGING: prototype SHA-512 compression functions with
//! the FEAT_SHA512 instructions, hand-written, timed on the CI runners to
//! choose what to implement (and verify) in Lean.

use criterion::Criterion;

pub const USES: &[&str] = &["sha512"];

#[cfg(target_arch = "aarch64")]
mod protos {
    /// Prototype `dblrot_keep`.
    #[unsafe(naked)]
    pub unsafe extern "C" fn dblrot_keep(_: *mut u64, _: *const u8, _: usize, _: *mut u64) {
        core::arch::naked_asm!(include_str!("sha512_proto/dblrot_keep.S"))
    }
    /// Prototype `dblrot_keep_ktab`.
    #[unsafe(naked)]
    pub unsafe extern "C" fn dblrot_keep_ktab(_: *mut u64, _: *const u8, _: usize, _: *mut u64) {
        core::arch::naked_asm!(include_str!("sha512_proto/dblrot_keep_ktab.S"))
    }
    /// Prototype `dblrot_ktabi2`.
    #[unsafe(naked)]
    pub unsafe extern "C" fn dblrot_ktabi2(_: *mut u64, _: *const u8, _: usize, _: *mut u64) {
        core::arch::naked_asm!(include_str!("sha512_proto/dblrot_ktabi2.S"))
    }
    /// Prototype `dblrot_ktabi4`.
    #[unsafe(naked)]
    pub unsafe extern "C" fn dblrot_ktabi4(_: *mut u64, _: *const u8, _: usize, _: *mut u64) {
        core::arch::naked_asm!(include_str!("sha512_proto/dblrot_ktabi4.S"))
    }
    /// Prototype `dblrot_ktabi8`.
    #[unsafe(naked)]
    pub unsafe extern "C" fn dblrot_ktabi8(_: *mut u64, _: *const u8, _: usize, _: *mut u64) {
        core::arch::naked_asm!(include_str!("sha512_proto/dblrot_ktabi8.S"))
    }
    /// Prototype `main`.
    #[unsafe(naked)]
    pub unsafe extern "C" fn main(_: *mut u64, _: *const u8, _: usize, _: *mut u64) {
        core::arch::naked_asm!(include_str!("sha512_proto/main.S"))
    }
    /// Prototype `pr592`.
    #[unsafe(naked)]
    pub unsafe extern "C" fn pr592(_: *mut u64, _: *const u8, _: usize, _: *mut u64) {
        core::arch::naked_asm!(include_str!("sha512_proto/pr592.S"))
    }
}

#[cfg(target_arch = "aarch64")]
type Compress = unsafe extern "C" fn(*mut u64, *const u8, usize, *mut u64);

#[cfg(target_arch = "aarch64")]
pub fn bench(c: &mut Criterion) {
    use criterion::{BenchmarkId, Throughput};
    use std::hint::black_box;
    if !std::arch::is_aarch64_feature_detected!("sha3") {
        return;
    }
    let protos: &[(&str, Compress)] = &[
        ("dblrot_keep", protos::dblrot_keep as Compress),
        ("dblrot_keep_ktab", protos::dblrot_keep_ktab as Compress),
        ("dblrot_ktabi2", protos::dblrot_ktabi2 as Compress),
        ("dblrot_ktabi4", protos::dblrot_ktabi4 as Compress),
        ("dblrot_ktabi8", protos::dblrot_ktabi8 as Compress),
        ("main", protos::main as Compress),
        ("pr592", protos::pr592 as Compress),
    ];
    let data = vec![0x5au8; 16384];
    let mut reference = None;
    for &(name, f) in protos {
        let mut state = [0u64; 8];
        let mut scratch = [0u64; 166];
        unsafe { f(state.as_mut_ptr(), data.as_ptr(), 128, scratch.as_mut_ptr()) };
        assert_eq!(*reference.get_or_insert(state), state, "{name} disagrees");
        let mut g = c.benchmark_group(format!("sha512-proto-{name}"));
        for blocks in [1usize, 8, 128] {
            g.throughput(Throughput::Bytes(128 * blocks as u64));
            g.bench_function(BenchmarkId::new(crate::VG, 128 * blocks), |b| {
                b.iter(|| unsafe {
                    f(
                        state.as_mut_ptr(),
                        black_box(data.as_ptr()),
                        blocks,
                        scratch.as_mut_ptr(),
                    )
                })
            });
        }
        g.finish();
    }
}

#[cfg(not(target_arch = "aarch64"))]
pub fn bench(_: &mut Criterion) {}
