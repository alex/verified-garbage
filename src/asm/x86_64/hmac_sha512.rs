// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `hmac_sha512` functions for `x86_64`.
#![allow(dead_code)]

/// Starts an HMAC-SHA-512 computation with a key of at most 128 bytes: makes the SHA-512 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 128 bytes (FIPS 198-1). The text is then absorbed with `vg_sha512_update` on `*inner` (its `count` starting at 128), and the MAC computed with `vg_hmac_sha512_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha512I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `key_len` must be at most 128.
/// * `inner` and `outer` must each be valid for reads and writes of 192 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 768 bytes; its contents on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha512_init(inner: *mut [u8; 192], outer: *mut [u8; 192], key: *const u8, key_len: usize, scratch: *mut [u64; 96]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+272], rbx",
        "mov QWORD PTR [r8+280], rbp",
        "mov QWORD PTR [r8+288], r12",
        "mov QWORD PTR [r8+296], r13",
        "mov QWORD PTR [r8+304], r14",
        "mov QWORD PTR [r8+312], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r15, r8",
        "mov rbp, rdx",
        "mov r13, rcx",
        "mov r14d, 0",
        "test r13, r13",
        "je 20f",
        "22:",
        "movzx eax, BYTE PTR [rbp+r14*1]",
        "mov ecx, eax",
        "xor eax, 54",
        "mov BYTE PTR [r15+r14*1+320], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+448], cl",
        "add r14, 1",
        "cmp r14, r13",
        "jne 22b",
        "jmp 21f",
        "20:",
        "21:",
        "mov eax, 54",
        "mov ecx, 92",
        "cmp r14, 128",
        "je 23f",
        "25:",
        "mov BYTE PTR [r15+r14*1+320], al",
        "mov BYTE PTR [r15+r14*1+448], cl",
        "add r14, 1",
        "cmp r14, 128",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rdi, rbx",
        "call {vg_sha512_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 320",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, r12",
        "call {vg_sha512_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 448",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rbx, QWORD PTR [r15+272]",
        "mov rbp, QWORD PTR [r15+280]",
        "mov r12, QWORD PTR [r15+288]",
        "mov r13, QWORD PTR [r15+296]",
        "mov r14, QWORD PTR [r15+304]",
        "mov r15, QWORD PTR [r15+312]",
        "ret",
        vg_sha512_init = sym super::sha512::vg_sha512_init,
        vg_sha512_update = sym super::sha512::vg_sha512_update,
    )
}

/// Finishes an HMAC-SHA-512 computation: if, for a 128-byte key `K₀` and a text of fewer than 2⁶⁴ − 128 bytes, the SHA-512 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-512 of the text under `K₀` (64 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha512I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 192 bytes; its contents on return are unspecified.
/// * `outer` must be valid for reads of 192 bytes.
/// * `out` must be valid for writes of 64 bytes.
/// * `scratch` must be valid for reads and writes of 768 bytes; its contents on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha512_finalize(inner: *mut [u8; 192], outer: *const [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 96]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+272], rbx",
        "mov QWORD PTR [r8+280], rbp",
        "mov QWORD PTR [r8+288], r12",
        "mov QWORD PTR [r8+296], r13",
        "mov QWORD PTR [r8+304], r14",
        "mov QWORD PTR [r8+312], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 320",
        "mov rcx, r15",
        "call {vg_sha512_finalize}",
        "mov r14d, 0",
        "20:",
        "movzx eax, BYTE PTR [r12+r14*1]",
        "mov BYTE PTR [rbx+r14*1], al",
        "add r14, 1",
        "cmp r14, 192",
        "jne 20b",
        "mov rdi, rbx",
        "mov esi, 128",
        "mov rdx, r15",
        "add rdx, 320",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, rbx",
        "mov esi, 192",
        "mov rdx, r15",
        "add rdx, 320",
        "mov rcx, r15",
        "call {vg_sha512_finalize}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+320]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 64",
        "jne 21b",
        "mov rbx, QWORD PTR [r15+272]",
        "mov rbp, QWORD PTR [r15+280]",
        "mov r12, QWORD PTR [r15+288]",
        "mov r13, QWORD PTR [r15+296]",
        "mov r14, QWORD PTR [r15+304]",
        "mov r15, QWORD PTR [r15+312]",
        "ret",
        vg_sha512_finalize = sym super::sha512::vg_sha512_finalize,
        vg_sha512_update = sym super::sha512::vg_sha512_update,
    )
}
