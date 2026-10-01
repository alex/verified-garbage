// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `ct` functions for `x86`.
#![allow(dead_code)]

/// Compares two byte strings in constant time: returns 1 if the `a_len` bytes at `a` are the `b_len` bytes at `b` (so byte strings of different lengths are unequal), and 0 otherwise. Writes no memory.
///
/// Contract: `VG.Spec.Ct.eqContract`. Constant time: only the pointers, `a_len` and `b_len` may affect timing, not the bytes compared; only the result depends on them.
///
/// # Safety
///
/// * `a` must be valid for reads of `a_len` bytes.
/// * `b` must be valid for reads of `b_len` bytes.
/// * Neither `a` nor `b` may overlap the return address on the stack or the 4 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_ct_eq(a: *const u8, a_len: usize, b: *const u8, b_len: usize) -> u32 {
    core::arch::naked_asm!(
        "push ebx",
        "mov eax, DWORD PTR [esp+12]",
        "mov edx, DWORD PTR [esp+20]",
        "cmp eax, edx",
        "je 20f",
        "mov eax, 0",
        "jmp 21f",
        "20:",
        "mov ebx, 0",
        "mov ecx, 0",
        "mov eax, DWORD PTR [esp+12]",
        "cmp ecx, eax",
        "je 22f",
        "24:",
        "mov eax, DWORD PTR [esp+8]",
        "add eax, ecx",
        "movzx edx, BYTE PTR [eax]",
        "mov eax, DWORD PTR [esp+16]",
        "add eax, ecx",
        "movzx eax, BYTE PTR [eax]",
        "xor edx, eax",
        "or ebx, edx",
        "add ecx, 1",
        "mov eax, DWORD PTR [esp+12]",
        "cmp ecx, eax",
        "jne 24b",
        "jmp 23f",
        "22:",
        "23:",
        "mov eax, ebx",
        "sub eax, 1",
        "shr eax, 31",
        "21:",
        "pop ebx",
        "ret",
    )
}
