// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `hmac_sha1` functions for `x86_64`.
#![allow(dead_code)]

/// Starts an HMAC-SHA-1 computation with a key of at most 64 bytes: makes the SHA-1 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_sha1_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_sha1_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha1I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 84 bytes.
/// * `outer` must be valid for reads and writes of 84 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 448 bytes.
/// * `key_len` must be at most 64.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha1_init(inner: *mut [u8; 84], outer: *mut [u8; 84], key: *const u8, key_len: usize, scratch: *mut [u64; 56]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+160], rbx",
        "mov QWORD PTR [r8+168], rbp",
        "mov QWORD PTR [r8+176], r12",
        "mov QWORD PTR [r8+184], r13",
        "mov QWORD PTR [r8+192], r14",
        "mov QWORD PTR [r8+200], r15",
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
        "mov BYTE PTR [r15+r14*1+208], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+272], cl",
        "add r14, 1",
        "cmp r14, r13",
        "jne 22b",
        "jmp 21f",
        "20:",
        "21:",
        "mov eax, 54",
        "mov ecx, 92",
        "cmp r14, 64",
        "je 23f",
        "25:",
        "mov BYTE PTR [r15+r14*1+208], al",
        "mov BYTE PTR [r15+r14*1+272], cl",
        "add r14, 1",
        "cmp r14, 64",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rdi, rbx",
        "call {vg_sha1_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 208",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha1_update}",
        "mov rdi, r12",
        "call {vg_sha1_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 272",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha1_update}",
        "mov rbx, QWORD PTR [r15+160]",
        "mov rbp, QWORD PTR [r15+168]",
        "mov r12, QWORD PTR [r15+176]",
        "mov r13, QWORD PTR [r15+184]",
        "mov r14, QWORD PTR [r15+192]",
        "mov r15, QWORD PTR [r15+200]",
        "ret",
        vg_sha1_init = sym super::sha1::vg_sha1_init,
        vg_sha1_update = sym super::sha1::vg_sha1_update,
    )
}

/// Finishes an HMAC-SHA-1 computation: if, for a 64-byte key `K₀` and a text of fewer than 2⁶⁴ − 64 bytes, the SHA-1 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-1 of the text under `K₀` (20 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha1I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 84 bytes.
/// * `outer` must be valid for reads of 84 bytes.
/// * `out` must be valid for reads and writes of 20 bytes.
/// * `scratch` must be valid for reads and writes of 448 bytes.
/// * The contents of `inner` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha1_finalize(inner: *mut [u8; 84], outer: *const [u8; 84], count: u64, out: *mut [u8; 20], scratch: *mut [u64; 56]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+160], rbx",
        "mov QWORD PTR [r8+168], rbp",
        "mov QWORD PTR [r8+176], r12",
        "mov QWORD PTR [r8+184], r13",
        "mov QWORD PTR [r8+192], r14",
        "mov QWORD PTR [r8+200], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 208",
        "mov rcx, r15",
        "call {vg_sha1_finalize}",
        "mov r14d, 0",
        "20:",
        "movzx eax, BYTE PTR [r12+r14*1]",
        "mov BYTE PTR [rbx+r14*1], al",
        "add r14, 1",
        "cmp r14, 84",
        "jne 20b",
        "mov rdi, rbx",
        "mov esi, 64",
        "mov rdx, r15",
        "add rdx, 208",
        "mov ecx, 20",
        "mov r8, r15",
        "call {vg_sha1_update}",
        "mov rdi, rbx",
        "mov esi, 84",
        "mov rdx, r15",
        "add rdx, 208",
        "mov rcx, r15",
        "call {vg_sha1_finalize}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+208]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 20",
        "jne 21b",
        "mov rbx, QWORD PTR [r15+160]",
        "mov rbp, QWORD PTR [r15+168]",
        "mov r12, QWORD PTR [r15+176]",
        "mov r13, QWORD PTR [r15+184]",
        "mov r14, QWORD PTR [r15+192]",
        "mov r15, QWORD PTR [r15+200]",
        "ret",
        vg_sha1_finalize = sym super::sha1::vg_sha1_finalize,
        vg_sha1_update = sym super::sha1::vg_sha1_update,
    )
}

/// The CPU features `vg_hmac_sha1_init_shani` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA1_INIT_SHANI_FEATURES: &[&str] = &["sha", "ssse3"];

/// Starts an HMAC-SHA-1 computation with a key of at most 64 bytes: makes the SHA-1 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_sha1_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_sha1_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha1I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 84 bytes.
/// * `outer` must be valid for reads and writes of 84 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 448 bytes.
/// * `key_len` must be at most 64.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `sha` and `ssse3` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha1_init_shani(inner: *mut [u8; 84], outer: *mut [u8; 84], key: *const u8, key_len: usize, scratch: *mut [u64; 56]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+160], rbx",
        "mov QWORD PTR [r8+168], rbp",
        "mov QWORD PTR [r8+176], r12",
        "mov QWORD PTR [r8+184], r13",
        "mov QWORD PTR [r8+192], r14",
        "mov QWORD PTR [r8+200], r15",
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
        "mov BYTE PTR [r15+r14*1+208], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+272], cl",
        "add r14, 1",
        "cmp r14, r13",
        "jne 22b",
        "jmp 21f",
        "20:",
        "21:",
        "mov eax, 54",
        "mov ecx, 92",
        "cmp r14, 64",
        "je 23f",
        "25:",
        "mov BYTE PTR [r15+r14*1+208], al",
        "mov BYTE PTR [r15+r14*1+272], cl",
        "add r14, 1",
        "cmp r14, 64",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rdi, rbx",
        "call {vg_sha1_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 208",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha1_update_shani}",
        "mov rdi, r12",
        "call {vg_sha1_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 272",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha1_update_shani}",
        "mov rbx, QWORD PTR [r15+160]",
        "mov rbp, QWORD PTR [r15+168]",
        "mov r12, QWORD PTR [r15+176]",
        "mov r13, QWORD PTR [r15+184]",
        "mov r14, QWORD PTR [r15+192]",
        "mov r15, QWORD PTR [r15+200]",
        "ret",
        vg_sha1_init = sym super::sha1::vg_sha1_init,
        vg_sha1_update_shani = sym super::sha1::vg_sha1_update_shani,
    )
}

/// The CPU features `vg_hmac_sha1_finalize_shani` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA1_FINALIZE_SHANI_FEATURES: &[&str] = &["sha", "ssse3"];

/// Finishes an HMAC-SHA-1 computation: if, for a 64-byte key `K₀` and a text of fewer than 2⁶⁴ − 64 bytes, the SHA-1 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-1 of the text under `K₀` (20 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha1I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 84 bytes.
/// * `outer` must be valid for reads of 84 bytes.
/// * `out` must be valid for reads and writes of 20 bytes.
/// * `scratch` must be valid for reads and writes of 448 bytes.
/// * The contents of `inner` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `sha` and `ssse3` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha1_finalize_shani(inner: *mut [u8; 84], outer: *const [u8; 84], count: u64, out: *mut [u8; 20], scratch: *mut [u64; 56]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+160], rbx",
        "mov QWORD PTR [r8+168], rbp",
        "mov QWORD PTR [r8+176], r12",
        "mov QWORD PTR [r8+184], r13",
        "mov QWORD PTR [r8+192], r14",
        "mov QWORD PTR [r8+200], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 208",
        "mov rcx, r15",
        "call {vg_sha1_finalize_shani}",
        "mov r14d, 0",
        "20:",
        "movzx eax, BYTE PTR [r12+r14*1]",
        "mov BYTE PTR [rbx+r14*1], al",
        "add r14, 1",
        "cmp r14, 84",
        "jne 20b",
        "mov rdi, rbx",
        "mov esi, 64",
        "mov rdx, r15",
        "add rdx, 208",
        "mov ecx, 20",
        "mov r8, r15",
        "call {vg_sha1_update_shani}",
        "mov rdi, rbx",
        "mov esi, 84",
        "mov rdx, r15",
        "add rdx, 208",
        "mov rcx, r15",
        "call {vg_sha1_finalize_shani}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+208]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 20",
        "jne 21b",
        "mov rbx, QWORD PTR [r15+160]",
        "mov rbp, QWORD PTR [r15+168]",
        "mov r12, QWORD PTR [r15+176]",
        "mov r13, QWORD PTR [r15+184]",
        "mov r14, QWORD PTR [r15+192]",
        "mov r15, QWORD PTR [r15+200]",
        "ret",
        vg_sha1_finalize_shani = sym super::sha1::vg_sha1_finalize_shani,
        vg_sha1_update_shani = sym super::sha1::vg_sha1_update_shani,
    )
}
