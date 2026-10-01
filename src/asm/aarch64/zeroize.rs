// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `zeroize` functions for `aarch64`.
#![allow(dead_code)]

/// Wipes a buffer: sets the `len` bytes at `p` to zero, and writes no other memory. A call of it is not a dead store the compiler may remove, since the compiler cannot see its code.
///
/// Contract: `VG.Spec.Zeroize.zeroizeContract`. Constant time: only `p` and `len` may affect timing, not the bytes wiped.
///
/// # Safety
///
/// * `p` must be valid for reads and writes of `len` bytes.
/// * `p` must not wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_zeroize(p: *mut u8, len: usize) {
    core::arch::naked_asm!(
        "movz x2, #0, lsl #0",
        "lsr x3, x1, #3",
        "movz x4, #7, lsl #0",
        "and x1, x1, x4",
        "cbz x3, 20f",
        "22:",
        "str x2, [x0, #0]",
        "add x0, x0, #8",
        "sub x3, x3, #1",
        "cbnz x3, 22b",
        "b 21f",
        "20:",
        "21:",
        "add x3, x1, #0",
        "cbz x3, 23f",
        "25:",
        "strb w2, [x0, #0]",
        "add x0, x0, #1",
        "sub x3, x3, #1",
        "cbnz x3, 25b",
        "b 24f",
        "23:",
        "24:",
        "ret",
    )
}
