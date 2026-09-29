// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `hmac_sha256` functions for `x86_64`.
#![allow(dead_code)]

/// Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.
///
/// Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `key_len` must be at most 64.
/// * `inner` and `outer` must each be valid for reads and writes of 96 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 608 bytes; its contents on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 8 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 76]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+560], rbx",
        "mov QWORD PTR [r8+568], rbp",
        "mov QWORD PTR [r8+576], r12",
        "mov QWORD PTR [r8+584], r13",
        "mov QWORD PTR [r8+592], r14",
        "mov QWORD PTR [r8+600], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r15, r8",
        "mov rbp, rdx",
        "mov r13, rcx",
        "mov eax, 1779033703",
        "mov DWORD PTR [rbx], eax",
        "mov eax, -1150833019",
        "mov DWORD PTR [rbx+4], eax",
        "mov eax, 1013904242",
        "mov DWORD PTR [rbx+8], eax",
        "mov eax, -1521486534",
        "mov DWORD PTR [rbx+12], eax",
        "mov eax, 1359893119",
        "mov DWORD PTR [rbx+16], eax",
        "mov eax, -1694144372",
        "mov DWORD PTR [rbx+20], eax",
        "mov eax, 528734635",
        "mov DWORD PTR [rbx+24], eax",
        "mov eax, 1541459225",
        "mov DWORD PTR [rbx+28], eax",
        "mov eax, 1779033703",
        "mov DWORD PTR [r12], eax",
        "mov eax, -1150833019",
        "mov DWORD PTR [r12+4], eax",
        "mov eax, 1013904242",
        "mov DWORD PTR [r12+8], eax",
        "mov eax, -1521486534",
        "mov DWORD PTR [r12+12], eax",
        "mov eax, 1359893119",
        "mov DWORD PTR [r12+16], eax",
        "mov eax, -1694144372",
        "mov DWORD PTR [r12+20], eax",
        "mov eax, 528734635",
        "mov DWORD PTR [r12+24], eax",
        "mov eax, 1541459225",
        "mov DWORD PTR [r12+28], eax",
        "mov r14d, 0",
        "test r13, r13",
        "je 20f",
        "22:",
        "movzx eax, BYTE PTR [rbp+r14*1]",
        "mov ecx, eax",
        "xor eax, 54",
        "mov BYTE PTR [rbx+r14*1+32], al",
        "xor ecx, 92",
        "mov BYTE PTR [r12+r14*1+32], cl",
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
        "mov BYTE PTR [rbx+r14*1+32], al",
        "mov BYTE PTR [r12+r14*1+32], cl",
        "add r14, 1",
        "cmp r14, 64",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rsi, rbx",
        "add rsi, 32",
        "mov rdi, rbx",
        "mov edx, 1",
        "mov rcx, r15",
        "call {vg_sha256_compress}",
        "mov rbx, rdi",
        "mov r15, rcx",
        "mov rbx, r12",
        "mov rsi, r12",
        "add rsi, 32",
        "mov rdi, rbx",
        "mov edx, 1",
        "mov rcx, r15",
        "call {vg_sha256_compress}",
        "mov rbx, rdi",
        "mov r15, rcx",
        "mov rbx, QWORD PTR [r15+560]",
        "mov rbp, QWORD PTR [r15+568]",
        "mov r12, QWORD PTR [r15+576]",
        "mov r13, QWORD PTR [r15+584]",
        "mov r14, QWORD PTR [r15+592]",
        "mov r15, QWORD PTR [r15+600]",
        "ret",
        vg_sha256_compress = sym super::sha256::vg_sha256_compress,
    )
}

/// Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the text under `K₀` in bytes 176 to 207 of `*scratch`.
///
/// Contract: `VG.Spec.Hmac.finalizeSha256Contract`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 96 bytes; its contents on return are unspecified.
/// * `outer` must be valid for reads of 96 bytes.
/// * `scratch` must be valid for reads and writes of 688 bytes; its contents on return are unspecified, apart from the MAC.
/// * `inner` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, scratch: *mut [u64; 86]) {
    core::arch::naked_asm!(
        "mov eax, DWORD PTR [rsi]",
        "mov DWORD PTR [rcx+640], eax",
        "mov eax, DWORD PTR [rsi+4]",
        "mov DWORD PTR [rcx+644], eax",
        "mov eax, DWORD PTR [rsi+8]",
        "mov DWORD PTR [rcx+648], eax",
        "mov eax, DWORD PTR [rsi+12]",
        "mov DWORD PTR [rcx+652], eax",
        "mov eax, DWORD PTR [rsi+16]",
        "mov DWORD PTR [rcx+656], eax",
        "mov eax, DWORD PTR [rsi+20]",
        "mov DWORD PTR [rcx+660], eax",
        "mov eax, DWORD PTR [rsi+24]",
        "mov DWORD PTR [rcx+664], eax",
        "mov eax, DWORD PTR [rsi+28]",
        "mov DWORD PTR [rcx+668], eax",
        "mov rsi, rdx",
        "mov rdx, rcx",
        "add rdx, 608",
        "call {vg_sha256_finalize}",
        "mov eax, DWORD PTR [rcx+640]",
        "mov DWORD PTR [rdi], eax",
        "mov eax, DWORD PTR [rcx+644]",
        "mov DWORD PTR [rdi+4], eax",
        "mov eax, DWORD PTR [rcx+648]",
        "mov DWORD PTR [rdi+8], eax",
        "mov eax, DWORD PTR [rcx+652]",
        "mov DWORD PTR [rdi+12], eax",
        "mov eax, DWORD PTR [rcx+656]",
        "mov DWORD PTR [rdi+16], eax",
        "mov eax, DWORD PTR [rcx+660]",
        "mov DWORD PTR [rdi+20], eax",
        "mov eax, DWORD PTR [rcx+664]",
        "mov DWORD PTR [rdi+24], eax",
        "mov eax, DWORD PTR [rcx+668]",
        "mov DWORD PTR [rdi+28], eax",
        "mov rax, QWORD PTR [rcx+608]",
        "mov QWORD PTR [rdi+32], rax",
        "mov rax, QWORD PTR [rcx+616]",
        "mov QWORD PTR [rdi+40], rax",
        "mov rax, QWORD PTR [rcx+624]",
        "mov QWORD PTR [rdi+48], rax",
        "mov rax, QWORD PTR [rcx+632]",
        "mov QWORD PTR [rdi+56], rax",
        "mov esi, 96",
        "mov rdx, rcx",
        "add rdx, 608",
        "call {vg_sha256_finalize}",
        "mov rax, QWORD PTR [rcx+608]",
        "mov QWORD PTR [rcx+176], rax",
        "mov rax, QWORD PTR [rcx+616]",
        "mov QWORD PTR [rcx+184], rax",
        "mov rax, QWORD PTR [rcx+624]",
        "mov QWORD PTR [rcx+192], rax",
        "mov rax, QWORD PTR [rcx+632]",
        "mov QWORD PTR [rcx+200], rax",
        "ret",
        vg_sha256_finalize = sym super::sha256::vg_sha256_finalize,
    )
}

/// The CPU features `vg_hmac_sha256_init_shani` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA256_INIT_SHANI_FEATURES: &[&str] = &["sha", "ssse3"];

/// Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.
///
/// Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `key_len` must be at most 64.
/// * `inner` and `outer` must each be valid for reads and writes of 96 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 608 bytes; its contents on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 8 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `sha` and `ssse3` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_init_shani(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 76]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+560], rbx",
        "mov QWORD PTR [r8+568], rbp",
        "mov QWORD PTR [r8+576], r12",
        "mov QWORD PTR [r8+584], r13",
        "mov QWORD PTR [r8+592], r14",
        "mov QWORD PTR [r8+600], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r15, r8",
        "mov rbp, rdx",
        "mov r13, rcx",
        "mov eax, 1779033703",
        "mov DWORD PTR [rbx], eax",
        "mov eax, -1150833019",
        "mov DWORD PTR [rbx+4], eax",
        "mov eax, 1013904242",
        "mov DWORD PTR [rbx+8], eax",
        "mov eax, -1521486534",
        "mov DWORD PTR [rbx+12], eax",
        "mov eax, 1359893119",
        "mov DWORD PTR [rbx+16], eax",
        "mov eax, -1694144372",
        "mov DWORD PTR [rbx+20], eax",
        "mov eax, 528734635",
        "mov DWORD PTR [rbx+24], eax",
        "mov eax, 1541459225",
        "mov DWORD PTR [rbx+28], eax",
        "mov eax, 1779033703",
        "mov DWORD PTR [r12], eax",
        "mov eax, -1150833019",
        "mov DWORD PTR [r12+4], eax",
        "mov eax, 1013904242",
        "mov DWORD PTR [r12+8], eax",
        "mov eax, -1521486534",
        "mov DWORD PTR [r12+12], eax",
        "mov eax, 1359893119",
        "mov DWORD PTR [r12+16], eax",
        "mov eax, -1694144372",
        "mov DWORD PTR [r12+20], eax",
        "mov eax, 528734635",
        "mov DWORD PTR [r12+24], eax",
        "mov eax, 1541459225",
        "mov DWORD PTR [r12+28], eax",
        "mov r14d, 0",
        "test r13, r13",
        "je 20f",
        "22:",
        "movzx eax, BYTE PTR [rbp+r14*1]",
        "mov ecx, eax",
        "xor eax, 54",
        "mov BYTE PTR [rbx+r14*1+32], al",
        "xor ecx, 92",
        "mov BYTE PTR [r12+r14*1+32], cl",
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
        "mov BYTE PTR [rbx+r14*1+32], al",
        "mov BYTE PTR [r12+r14*1+32], cl",
        "add r14, 1",
        "cmp r14, 64",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rsi, rbx",
        "add rsi, 32",
        "mov rdi, rbx",
        "mov edx, 1",
        "mov rcx, r15",
        "call {vg_sha256_compress_shani}",
        "mov rbx, rdi",
        "mov r15, rcx",
        "mov rbx, r12",
        "mov rsi, r12",
        "add rsi, 32",
        "mov rdi, rbx",
        "mov edx, 1",
        "mov rcx, r15",
        "call {vg_sha256_compress_shani}",
        "mov rbx, rdi",
        "mov r15, rcx",
        "mov rbx, QWORD PTR [r15+560]",
        "mov rbp, QWORD PTR [r15+568]",
        "mov r12, QWORD PTR [r15+576]",
        "mov r13, QWORD PTR [r15+584]",
        "mov r14, QWORD PTR [r15+592]",
        "mov r15, QWORD PTR [r15+600]",
        "ret",
        vg_sha256_compress_shani = sym super::sha256::vg_sha256_compress_shani,
    )
}

/// The CPU features `vg_hmac_sha256_finalize_shani` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES: &[&str] = &["sha", "ssse3"];

/// Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text, the SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and `*outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the text under `K₀` in bytes 176 to 207 of `*scratch`.
///
/// Contract: `VG.Spec.Hmac.finalizeSha256Contract`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 96 bytes; its contents on return are unspecified.
/// * `outer` must be valid for reads of 96 bytes.
/// * `scratch` must be valid for reads and writes of 688 bytes; its contents on return are unspecified, apart from the MAC.
/// * `inner` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `sha` and `ssse3` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_finalize_shani(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, scratch: *mut [u64; 86]) {
    core::arch::naked_asm!(
        "mov eax, DWORD PTR [rsi]",
        "mov DWORD PTR [rcx+640], eax",
        "mov eax, DWORD PTR [rsi+4]",
        "mov DWORD PTR [rcx+644], eax",
        "mov eax, DWORD PTR [rsi+8]",
        "mov DWORD PTR [rcx+648], eax",
        "mov eax, DWORD PTR [rsi+12]",
        "mov DWORD PTR [rcx+652], eax",
        "mov eax, DWORD PTR [rsi+16]",
        "mov DWORD PTR [rcx+656], eax",
        "mov eax, DWORD PTR [rsi+20]",
        "mov DWORD PTR [rcx+660], eax",
        "mov eax, DWORD PTR [rsi+24]",
        "mov DWORD PTR [rcx+664], eax",
        "mov eax, DWORD PTR [rsi+28]",
        "mov DWORD PTR [rcx+668], eax",
        "mov rsi, rdx",
        "mov rdx, rcx",
        "add rdx, 608",
        "call {vg_sha256_finalize_shani}",
        "mov eax, DWORD PTR [rcx+640]",
        "mov DWORD PTR [rdi], eax",
        "mov eax, DWORD PTR [rcx+644]",
        "mov DWORD PTR [rdi+4], eax",
        "mov eax, DWORD PTR [rcx+648]",
        "mov DWORD PTR [rdi+8], eax",
        "mov eax, DWORD PTR [rcx+652]",
        "mov DWORD PTR [rdi+12], eax",
        "mov eax, DWORD PTR [rcx+656]",
        "mov DWORD PTR [rdi+16], eax",
        "mov eax, DWORD PTR [rcx+660]",
        "mov DWORD PTR [rdi+20], eax",
        "mov eax, DWORD PTR [rcx+664]",
        "mov DWORD PTR [rdi+24], eax",
        "mov eax, DWORD PTR [rcx+668]",
        "mov DWORD PTR [rdi+28], eax",
        "mov rax, QWORD PTR [rcx+608]",
        "mov QWORD PTR [rdi+32], rax",
        "mov rax, QWORD PTR [rcx+616]",
        "mov QWORD PTR [rdi+40], rax",
        "mov rax, QWORD PTR [rcx+624]",
        "mov QWORD PTR [rdi+48], rax",
        "mov rax, QWORD PTR [rcx+632]",
        "mov QWORD PTR [rdi+56], rax",
        "mov esi, 96",
        "mov rdx, rcx",
        "add rdx, 608",
        "call {vg_sha256_finalize_shani}",
        "mov rax, QWORD PTR [rcx+608]",
        "mov QWORD PTR [rcx+176], rax",
        "mov rax, QWORD PTR [rcx+616]",
        "mov QWORD PTR [rcx+184], rax",
        "mov rax, QWORD PTR [rcx+624]",
        "mov QWORD PTR [rcx+192], rax",
        "mov rax, QWORD PTR [rcx+632]",
        "mov QWORD PTR [rcx+200], rax",
        "ret",
        vg_sha256_finalize_shani = sym super::sha256::vg_sha256_finalize_shani,
    )
}
