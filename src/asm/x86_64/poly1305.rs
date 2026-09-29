// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `poly1305` functions for `x86_64`.
#![allow(dead_code)]

/// Starts a Poly1305 computation (RFC 8439 §2.5): makes the streaming state `*state` represent the empty message under the 32-byte one-time key `*key`.
///
/// Contract: `VG.Spec.Poly1305.initContract`. The streaming state is the accumulator followed by the key (`VG.Spec.Poly1305.Repr`). Constant time: only the pointers may affect timing, not the key.
///
/// # Safety
///
/// * `state` must be valid for writes of 128 bytes.
/// * `key` must be valid for reads of 32 bytes.
/// * `state` must not overlap `key` (distinct Rust objects never do).
/// * Neither `state` nor `key` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32]) {
    core::arch::naked_asm!(
        "mov rax, QWORD PTR [rsi]",
        "mov rcx, QWORD PTR [rsi+8]",
        "mov rdx, QWORD PTR [rsi+16]",
        "mov r8, QWORD PTR [rsi+24]",
        "mov QWORD PTR [rdi+24], rax",
        "mov QWORD PTR [rdi+32], rcx",
        "mov QWORD PTR [rdi+40], rdx",
        "mov QWORD PTR [rdi+48], r8",
        "mov eax, 0",
        "mov QWORD PTR [rdi], rax",
        "mov QWORD PTR [rdi+8], rax",
        "mov QWORD PTR [rdi+16], rax",
        "ret",
    )
}

/// Absorbs whole blocks into a Poly1305 computation: if the streaming state `*state` represents a message under a key, it then represents that message followed by the `n` 16-byte blocks at `blocks`, under the same key.
///
/// Contract: `VG.Spec.Poly1305.blocksContract`. Constant time: only the pointers and `n` may affect timing, not the state or the data.
///
/// # Safety
///
/// * `state` must be valid for reads and writes of 128 bytes.
/// * `blocks` must be valid for reads of `16 * n` bytes.
/// * `state` must not overlap `blocks` (distinct Rust objects never do).
/// * Neither `state` nor `blocks` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize) {
    core::arch::naked_asm!(
        "mov QWORD PTR [rdi+56], rbx",
        "mov QWORD PTR [rdi+64], rbp",
        "mov QWORD PTR [rdi+72], r12",
        "mov QWORD PTR [rdi+80], r13",
        "mov QWORD PTR [rdi+88], r14",
        "mov QWORD PTR [rdi+96], r15",
        "mov rcx, rdx",
        "movabs rax, 1152921487695413247",
        "mov r8, QWORD PTR [rdi+24]",
        "and r8, rax",
        "movabs rax, 1152921487695413244",
        "mov r9, QWORD PTR [rdi+32]",
        "and r9, rax",
        "mov r10, r9",
        "shr r10, 2",
        "add r10, r9",
        "mov r11, QWORD PTR [rdi]",
        "mov rbx, QWORD PTR [rdi+8]",
        "mov rbp, QWORD PTR [rdi+16]",
        "test rcx, rcx",
        "je 20f",
        "22:",
        "add r11, QWORD PTR [rsi]",
        "adc rbx, QWORD PTR [rsi+8]",
        "adc rbp, 1",
        "mov rax, r11",
        "mul r8",
        "mov r12, rax",
        "mov r13, rdx",
        "mov rax, rbx",
        "mul r10",
        "add r12, rax",
        "adc r13, rdx",
        "mov rax, r11",
        "mul r9",
        "mov r14, rax",
        "mov r15, rdx",
        "mov rax, rbx",
        "mul r8",
        "add r14, rax",
        "adc r15, rdx",
        "mov rax, rbp",
        "mul r10",
        "add r14, rax",
        "adc r15, rdx",
        "mov rax, rbp",
        "mul r8",
        "add r14, r13",
        "adc r15, rax",
        "mov r11, r12",
        "mov rbx, r14",
        "mov rbp, r15",
        "and rbp, 3",
        "mov rax, r15",
        "sub rax, rbp",
        "shr r15, 2",
        "add rax, r15",
        "add r11, rax",
        "adc rbx, 0",
        "adc rbp, 0",
        "add rsi, 16",
        "sub rcx, 1",
        "jne 22b",
        "jmp 21f",
        "20:",
        "21:",
        "mov rax, r11",
        "add rax, 5",
        "mov rdx, rbx",
        "adc rdx, 0",
        "mov r12, rbp",
        "adc r12, 0",
        "mov r13, r12",
        "shr r13, 2",
        "mov r14d, 0",
        "sub r14, r13",
        "and r12, 3",
        "xor rax, r11",
        "and rax, r14",
        "xor r11, rax",
        "xor rdx, rbx",
        "and rdx, r14",
        "xor rbx, rdx",
        "xor r12, rbp",
        "and r12, r14",
        "xor rbp, r12",
        "mov QWORD PTR [rdi], r11",
        "mov QWORD PTR [rdi+8], rbx",
        "mov QWORD PTR [rdi+16], rbp",
        "mov rbx, QWORD PTR [rdi+56]",
        "mov rbp, QWORD PTR [rdi+64]",
        "mov r12, QWORD PTR [rdi+72]",
        "mov r13, QWORD PTR [rdi+80]",
        "mov r14, QWORD PTR [rdi+88]",
        "mov r15, QWORD PTR [rdi+96]",
        "ret",
    )
}

/// Finishes a Poly1305 computation: if the streaming state `*state` represents a message under a key, writes the tag of that message followed by the `len` bytes at `tail`, under that key, to `*out`.
///
/// Contract: `VG.Spec.Poly1305.finalizeTailContract`. Constant time: only the pointers and `len` may affect timing, not the state or the data.
///
/// # Safety
///
/// * `len` must be less than 16.
/// * `state` must be valid for reads and writes of 128 bytes; its contents on return are unspecified.
/// * `tail` must be valid for reads of `len` bytes.
/// * `out` must be valid for writes of 16 bytes.
/// * `state` and `out` must not overlap each other or `tail` (distinct Rust objects never do).
/// * None of `state`, `tail` and `out` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_poly1305_finalize(state: *mut [u64; 16], tail: *const u8, len: usize, out: *mut [u8; 16]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [rdi+56], rbx",
        "mov QWORD PTR [rdi+64], rbp",
        "mov QWORD PTR [rdi+72], r12",
        "mov QWORD PTR [rdi+80], r13",
        "mov QWORD PTR [rdi+88], r14",
        "mov QWORD PTR [rdi+96], r15",
        "movabs rax, 1152921487695413247",
        "mov r8, QWORD PTR [rdi+24]",
        "and r8, rax",
        "movabs rax, 1152921487695413244",
        "mov r9, QWORD PTR [rdi+32]",
        "and r9, rax",
        "mov r10, r9",
        "shr r10, 2",
        "add r10, r9",
        "mov r11, QWORD PTR [rdi]",
        "mov rbx, QWORD PTR [rdi+8]",
        "mov rbp, QWORD PTR [rdi+16]",
        "test rdx, rdx",
        "je 20f",
        "mov eax, 0",
        "mov QWORD PTR [rdi+104], rax",
        "mov QWORD PTR [rdi+112], rax",
        "mov r12d, 0",
        "22:",
        "movzx eax, BYTE PTR [rsi+r12*1]",
        "mov BYTE PTR [rdi+r12*1+104], al",
        "add r12, 1",
        "cmp r12, rdx",
        "jne 22b",
        "mov eax, 1",
        "mov BYTE PTR [rdi+rdx*1+104], al",
        "mov rsi, rdi",
        "add rsi, 104",
        "add r11, QWORD PTR [rsi]",
        "adc rbx, QWORD PTR [rsi+8]",
        "adc rbp, 0",
        "mov rax, r11",
        "mul r8",
        "mov r12, rax",
        "mov r13, rdx",
        "mov rax, rbx",
        "mul r10",
        "add r12, rax",
        "adc r13, rdx",
        "mov rax, r11",
        "mul r9",
        "mov r14, rax",
        "mov r15, rdx",
        "mov rax, rbx",
        "mul r8",
        "add r14, rax",
        "adc r15, rdx",
        "mov rax, rbp",
        "mul r10",
        "add r14, rax",
        "adc r15, rdx",
        "mov rax, rbp",
        "mul r8",
        "add r14, r13",
        "adc r15, rax",
        "mov r11, r12",
        "mov rbx, r14",
        "mov rbp, r15",
        "and rbp, 3",
        "mov rax, r15",
        "sub rax, rbp",
        "shr r15, 2",
        "add rax, r15",
        "add r11, rax",
        "adc rbx, 0",
        "adc rbp, 0",
        "jmp 21f",
        "20:",
        "21:",
        "mov rax, r11",
        "add rax, 5",
        "mov rdx, rbx",
        "adc rdx, 0",
        "mov r12, rbp",
        "adc r12, 0",
        "mov r13, r12",
        "shr r13, 2",
        "mov r14d, 0",
        "sub r14, r13",
        "and r12, 3",
        "xor rax, r11",
        "and rax, r14",
        "xor r11, rax",
        "xor rdx, rbx",
        "and rdx, r14",
        "xor rbx, rdx",
        "xor r12, rbp",
        "and r12, r14",
        "xor rbp, r12",
        "add r11, QWORD PTR [rdi+40]",
        "adc rbx, QWORD PTR [rdi+48]",
        "mov QWORD PTR [rcx], r11",
        "mov QWORD PTR [rcx+8], rbx",
        "mov rbx, QWORD PTR [rdi+56]",
        "mov rbp, QWORD PTR [rdi+64]",
        "mov r12, QWORD PTR [rdi+72]",
        "mov r13, QWORD PTR [rdi+80]",
        "mov r14, QWORD PTR [rdi+88]",
        "mov r15, QWORD PTR [rdi+96]",
        "ret",
    )
}
