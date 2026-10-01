// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `ct` functions for `arm`.
#![allow(dead_code)]

/// Compares two byte strings in constant time: returns 1 if the `a_len` bytes at `a` are the `b_len` bytes at `b` (so byte strings of different lengths are unequal), and 0 otherwise. Writes no memory.
///
/// Contract: `VG.Spec.Ct.eqContract`. Constant time: only the pointers, `a_len` and `b_len` may affect timing, not the bytes compared; only the result depends on them.
///
/// # Safety
///
/// * `a` must be valid for reads of `a_len` bytes.
/// * `b` must be valid for reads of `b_len` bytes.
/// * Neither `a` nor `b` may overlap the 4 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_ct_eq(a: *const u8, a_len: usize, b: *const u8, b_len: usize) -> u32 {
    core::arch::naked_asm!(
        "push {{r4}}",
        "cmp r1, r3",
        "beq 20f",
        "mov r0, #0",
        "b 21f",
        "20:",
        "mov r3, #0",
        "cmp r1, #0",
        "beq 22f",
        "24:",
        "ldrb r12, [r0, #0]",
        "ldrb r4, [r2, #0]",
        "eor r12, r12, r4",
        "orr r3, r3, r12",
        "add r0, r0, #1",
        "add r2, r2, #1",
        "subs r1, r1, #1",
        "bne 24b",
        "b 23f",
        "22:",
        "23:",
        "sub r3, r3, #1",
        "lsr r0, r3, #31",
        "21:",
        "ldr r4, [sp], #4",
        "bx lr",
    )
}
