// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `hmac_md5` functions for `x86_64`.
#![allow(dead_code)]

/// Starts an HMAC-MD5 computation with a key of any length: makes the MD5 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` (or their MD5 digest, if there are more than 64) padded with zeros to 64 bytes (FIPS 198-1 §4, steps 1–3). The text is then absorbed with `vg_md5_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_md5_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initAnyKeyContract` of `VG.Spec.Hmac.md5I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 80 bytes.
/// * `outer` must be valid for reads and writes of 80 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 1024 bytes.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_md5_init(inner: *mut [u8; 80], outer: *mut [u8; 80], key: *const u8, key_len: usize, scratch: *mut [u64; 128]) {
    core::arch::naked_asm!(
        "cmp rcx, 65",
        "jb 20f",
        "mov QWORD PTR [r8+112], rbx",
        "mov QWORD PTR [r8+120], rbp",
        "mov QWORD PTR [r8+128], r12",
        "mov QWORD PTR [r8+136], r13",
        "mov QWORD PTR [r8+144], r14",
        "mov QWORD PTR [r8+152], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r15, r8",
        "mov rbp, rdx",
        "mov r13, rcx",
        "mov rdi, r15",
        "add rdi, 288",
        "call {vg_md5_init}",
        "mov rdi, r15",
        "add rdi, 288",
        "mov esi, 0",
        "mov rdx, rbp",
        "mov rcx, r13",
        "mov r8, r15",
        "call {vg_md5_update}",
        "mov rdi, r15",
        "add rdi, 288",
        "mov rsi, r13",
        "mov rdx, r15",
        "add rdx, 368",
        "mov rcx, r15",
        "call {vg_md5_finalize}",
        "mov rdi, rbx",
        "mov rsi, r12",
        "mov r8, r15",
        "mov rdx, r15",
        "add rdx, 368",
        "mov ecx, 16",
        "mov rbx, QWORD PTR [r15+112]",
        "mov rbp, QWORD PTR [r15+120]",
        "mov r12, QWORD PTR [r15+128]",
        "mov r13, QWORD PTR [r15+136]",
        "mov r14, QWORD PTR [r15+144]",
        "mov r15, QWORD PTR [r15+152]",
        "jmp 21f",
        "20:",
        "21:",
        "mov QWORD PTR [r8+112], rbx",
        "mov QWORD PTR [r8+120], rbp",
        "mov QWORD PTR [r8+128], r12",
        "mov QWORD PTR [r8+136], r13",
        "mov QWORD PTR [r8+144], r14",
        "mov QWORD PTR [r8+152], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r15, r8",
        "mov rbp, rdx",
        "mov r13, rcx",
        "mov r14d, 0",
        "test r13, r13",
        "je 22f",
        "24:",
        "movzx eax, BYTE PTR [rbp+r14*1]",
        "mov ecx, eax",
        "xor eax, 54",
        "mov BYTE PTR [r15+r14*1+160], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+224], cl",
        "add r14, 1",
        "cmp r14, r13",
        "jne 24b",
        "jmp 23f",
        "22:",
        "23:",
        "mov eax, 54",
        "mov ecx, 92",
        "cmp r14, 64",
        "je 25f",
        "27:",
        "mov BYTE PTR [r15+r14*1+160], al",
        "mov BYTE PTR [r15+r14*1+224], cl",
        "add r14, 1",
        "cmp r14, 64",
        "jne 27b",
        "jmp 26f",
        "25:",
        "26:",
        "mov rdi, rbx",
        "call {vg_md5_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 160",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_md5_update}",
        "mov rdi, r12",
        "call {vg_md5_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 224",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_md5_update}",
        "mov rbx, QWORD PTR [r15+112]",
        "mov rbp, QWORD PTR [r15+120]",
        "mov r12, QWORD PTR [r15+128]",
        "mov r13, QWORD PTR [r15+136]",
        "mov r14, QWORD PTR [r15+144]",
        "mov r15, QWORD PTR [r15+152]",
        "ret",
        vg_md5_init = sym super::md5::vg_md5_init,
        vg_md5_update = sym super::md5::vg_md5_update,
        vg_md5_finalize = sym super::md5::vg_md5_finalize,
    )
}

/// Finishes an HMAC-MD5 computation: if, for a 64-byte key `K₀` and a text of fewer than 2⁶⁴ − 64 bytes, the MD5 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-MD5 of the text under `K₀` (16 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.md5I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 80 bytes.
/// * `outer` must be valid for reads of 80 bytes.
/// * `out` must be valid for reads and writes of 16 bytes.
/// * `scratch` must be valid for reads and writes of 384 bytes.
/// * The contents of `inner` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_md5_finalize(inner: *mut [u8; 80], outer: *const [u8; 80], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 48]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+112], rbx",
        "mov QWORD PTR [r8+120], rbp",
        "mov QWORD PTR [r8+128], r12",
        "mov QWORD PTR [r8+136], r13",
        "mov QWORD PTR [r8+144], r14",
        "mov QWORD PTR [r8+152], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 160",
        "mov rcx, r15",
        "call {vg_md5_finalize}",
        "mov eax, DWORD PTR [r12]",
        "mov DWORD PTR [rbx], eax",
        "mov eax, DWORD PTR [r12+4]",
        "mov DWORD PTR [rbx+4], eax",
        "mov eax, DWORD PTR [r12+8]",
        "mov DWORD PTR [rbx+8], eax",
        "mov eax, DWORD PTR [r12+12]",
        "mov DWORD PTR [rbx+12], eax",
        "mov eax, DWORD PTR [r15+160]",
        "mov DWORD PTR [rbx+16], eax",
        "mov eax, DWORD PTR [r15+164]",
        "mov DWORD PTR [rbx+20], eax",
        "mov eax, DWORD PTR [r15+168]",
        "mov DWORD PTR [rbx+24], eax",
        "mov eax, DWORD PTR [r15+172]",
        "mov DWORD PTR [rbx+28], eax",
        "mov rdi, rbx",
        "mov esi, 80",
        "mov rdx, r15",
        "add rdx, 160",
        "mov rcx, r15",
        "call {vg_md5_finalize}",
        "mov eax, DWORD PTR [r15+160]",
        "mov DWORD PTR [r13], eax",
        "mov eax, DWORD PTR [r15+164]",
        "mov DWORD PTR [r13+4], eax",
        "mov eax, DWORD PTR [r15+168]",
        "mov DWORD PTR [r13+8], eax",
        "mov eax, DWORD PTR [r15+172]",
        "mov DWORD PTR [r13+12], eax",
        "mov rbx, QWORD PTR [r15+112]",
        "mov rbp, QWORD PTR [r15+120]",
        "mov r12, QWORD PTR [r15+128]",
        "mov r13, QWORD PTR [r15+136]",
        "mov r14, QWORD PTR [r15+144]",
        "mov r15, QWORD PTR [r15+152]",
        "ret",
        vg_md5_finalize = sym super::md5::vg_md5_finalize,
    )
}
