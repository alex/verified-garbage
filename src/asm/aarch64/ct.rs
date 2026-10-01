// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `ct` functions for `aarch64`.
#![allow(dead_code)]

/// Compares two byte strings in constant time: returns 1 if the `a_len` bytes at `a` are the `b_len` bytes at `b` (so byte strings of different lengths are unequal), and 0 otherwise. Writes no memory.
///
/// Contract: `VG.Spec.Ct.eqContract`. Constant time: only the pointers, `a_len` and `b_len` may affect timing, not the bytes compared; only the result depends on them.
///
/// # Safety
///
/// * `a` must be valid for reads of `a_len` bytes.
/// * `b` must be valid for reads of `b_len` bytes.
/// * Neither `a` nor `b` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_ct_eq(a: *const u8, a_len: usize, b: *const u8, b_len: usize) -> u32 {
    core::arch::naked_asm!(
        "movz x4, #0, lsl #0",
        "sub x9, x1, x3",
        "cbz x9, 20f",
        "movz w0, #0, lsl #0",
        "b 21f",
        "20:",
        "movz x8, #0, lsl #0",
        "cbz x1, 22f",
        "24:",
        "add x5, x0, x8",
        "ldrb w6, [x5, #0]",
        "add x5, x2, x8",
        "ldrb w7, [x5, #0]",
        "eor x6, x6, x7",
        "orr x4, x4, x6",
        "add x8, x8, #1",
        "sub x9, x8, x1",
        "cbnz x9, 24b",
        "b 23f",
        "22:",
        "23:",
        "sub x4, x4, #1",
        "lsr x0, x4, #63",
        "21:",
        "ret",
    )
}
