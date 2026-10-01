// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `zeroize` functions for `x86_64`.
#![allow(dead_code)]

/// Wipes a buffer: sets the `len` bytes at `p` to zero, and writes no other memory. A call of it is not a dead store the compiler may remove, since the compiler cannot see its code.
///
/// Contract: `VG.Spec.Zeroize.zeroizeContract`. Constant time: only `p` and `len` may affect timing, not the bytes wiped.
///
/// # Safety
///
/// * `p` must be valid for reads and writes of `len` bytes.
/// * `p` must not overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_zeroize(p: *mut u8, len: usize) {
    core::arch::naked_asm!(
        "mov rax, 0",
        "mov rdx, rsi",
        "shr rdx, 3",
        "and rsi, 7",
        "cmp rdx, 0",
        "je 20f",
        "22:",
        "mov QWORD PTR [rdi], rax",
        "add rdi, 8",
        "sub rdx, 1",
        "jne 22b",
        "jmp 21f",
        "20:",
        "21:",
        "mov rdx, rsi",
        "cmp rdx, 0",
        "je 23f",
        "25:",
        "mov BYTE PTR [rdi], al",
        "add rdi, 1",
        "sub rdx, 1",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "ret",
    )
}
