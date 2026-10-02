// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `hmac_sha256` functions for `x86_64`.
#![allow(dead_code)]

/// Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha256I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 96 bytes.
/// * `outer` must be valid for reads and writes of 96 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 832 bytes.
/// * `key_len` must be at most 64.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+608], rbx",
        "mov QWORD PTR [r8+616], rbp",
        "mov QWORD PTR [r8+624], r12",
        "mov QWORD PTR [r8+632], r13",
        "mov QWORD PTR [r8+640], r14",
        "mov QWORD PTR [r8+648], r15",
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
        "mov BYTE PTR [r15+r14*1+656], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+720], cl",
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
        "mov BYTE PTR [r15+r14*1+656], al",
        "mov BYTE PTR [r15+r14*1+720], cl",
        "add r14, 1",
        "cmp r14, 64",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rdi, rbx",
        "call {vg_sha256_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 656",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha256_update}",
        "mov rdi, r12",
        "call {vg_sha256_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 720",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha256_update}",
        "mov rbx, QWORD PTR [r15+608]",
        "mov rbp, QWORD PTR [r15+616]",
        "mov r12, QWORD PTR [r15+624]",
        "mov r13, QWORD PTR [r15+632]",
        "mov r14, QWORD PTR [r15+640]",
        "mov r15, QWORD PTR [r15+648]",
        "ret",
        vg_sha256_init = sym super::sha256::vg_sha256_init,
        vg_sha256_update = sym super::sha256::vg_sha256_update,
    )
}

/// Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text of fewer than 2⁶⁴ − 64 bytes, the SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the text under `K₀` (32 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha256I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 96 bytes.
/// * `outer` must be valid for reads of 96 bytes.
/// * `out` must be valid for reads and writes of 32 bytes.
/// * `scratch` must be valid for reads and writes of 832 bytes.
/// * The contents of `inner` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+608], rbx",
        "mov QWORD PTR [r8+616], rbp",
        "mov QWORD PTR [r8+624], r12",
        "mov QWORD PTR [r8+632], r13",
        "mov QWORD PTR [r8+640], r14",
        "mov QWORD PTR [r8+648], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 656",
        "mov rcx, r15",
        "call {vg_sha256_finalize}",
        "mov eax, DWORD PTR [r12]",
        "mov DWORD PTR [rbx], eax",
        "mov eax, DWORD PTR [r12+4]",
        "mov DWORD PTR [rbx+4], eax",
        "mov eax, DWORD PTR [r12+8]",
        "mov DWORD PTR [rbx+8], eax",
        "mov eax, DWORD PTR [r12+12]",
        "mov DWORD PTR [rbx+12], eax",
        "mov eax, DWORD PTR [r12+16]",
        "mov DWORD PTR [rbx+16], eax",
        "mov eax, DWORD PTR [r12+20]",
        "mov DWORD PTR [rbx+20], eax",
        "mov eax, DWORD PTR [r12+24]",
        "mov DWORD PTR [rbx+24], eax",
        "mov eax, DWORD PTR [r12+28]",
        "mov DWORD PTR [rbx+28], eax",
        "mov eax, DWORD PTR [r15+656]",
        "mov DWORD PTR [rbx+32], eax",
        "mov eax, DWORD PTR [r15+660]",
        "mov DWORD PTR [rbx+36], eax",
        "mov eax, DWORD PTR [r15+664]",
        "mov DWORD PTR [rbx+40], eax",
        "mov eax, DWORD PTR [r15+668]",
        "mov DWORD PTR [rbx+44], eax",
        "mov eax, DWORD PTR [r15+672]",
        "mov DWORD PTR [rbx+48], eax",
        "mov eax, DWORD PTR [r15+676]",
        "mov DWORD PTR [rbx+52], eax",
        "mov eax, DWORD PTR [r15+680]",
        "mov DWORD PTR [rbx+56], eax",
        "mov eax, DWORD PTR [r15+684]",
        "mov DWORD PTR [rbx+60], eax",
        "mov rbp, rbx",
        "add rbp, 32",
        "mov eax, 128",
        "mov DWORD PTR [rbp+32], eax",
        "mov eax, 0",
        "mov DWORD PTR [rbp+36], eax",
        "mov DWORD PTR [rbp+40], eax",
        "mov DWORD PTR [rbp+44], eax",
        "mov DWORD PTR [rbp+48], eax",
        "mov DWORD PTR [rbp+52], eax",
        "mov r12d, 96",
        "mov rax, r12",
        "add rax, rax",
        "add rax, rax",
        "add rax, rax",
        "bswap rax",
        "mov QWORD PTR [rbx+88], rax",
        "mov rsi, rbp",
        "mov rdi, rbx",
        "mov edx, 1",
        "mov rcx, r15",
        "call {vg_sha256_compress}",
        "mov rbx, rdi",
        "mov r15, rcx",
        "mov rbp, r13",
        "mov eax, DWORD PTR [rbx]",
        "bswap eax",
        "mov DWORD PTR [rbp], eax",
        "mov eax, DWORD PTR [rbx+4]",
        "bswap eax",
        "mov DWORD PTR [rbp+4], eax",
        "mov eax, DWORD PTR [rbx+8]",
        "bswap eax",
        "mov DWORD PTR [rbp+8], eax",
        "mov eax, DWORD PTR [rbx+12]",
        "bswap eax",
        "mov DWORD PTR [rbp+12], eax",
        "mov eax, DWORD PTR [rbx+16]",
        "bswap eax",
        "mov DWORD PTR [rbp+16], eax",
        "mov eax, DWORD PTR [rbx+20]",
        "bswap eax",
        "mov DWORD PTR [rbp+20], eax",
        "mov eax, DWORD PTR [rbx+24]",
        "bswap eax",
        "mov DWORD PTR [rbp+24], eax",
        "mov eax, DWORD PTR [rbx+28]",
        "bswap eax",
        "mov DWORD PTR [rbp+28], eax",
        "mov rbx, QWORD PTR [r15+608]",
        "mov rbp, QWORD PTR [r15+616]",
        "mov r12, QWORD PTR [r15+624]",
        "mov r13, QWORD PTR [r15+632]",
        "mov r14, QWORD PTR [r15+640]",
        "mov r15, QWORD PTR [r15+648]",
        "ret",
        vg_sha256_finalize = sym super::sha256::vg_sha256_finalize,
        vg_sha256_compress = sym super::sha256::vg_sha256_compress,
    )
}

/// The CPU features `vg_hmac_sha256_init_avx2` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA256_INIT_AVX2_FEATURES: &[&str] = &["avx", "avx2", "bmi1", "bmi2"];

/// Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha256I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 96 bytes.
/// * `outer` must be valid for reads and writes of 96 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 832 bytes.
/// * `key_len` must be at most 64.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `avx`, `avx2`, `bmi1` and `bmi2` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_init_avx2(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+608], rbx",
        "mov QWORD PTR [r8+616], rbp",
        "mov QWORD PTR [r8+624], r12",
        "mov QWORD PTR [r8+632], r13",
        "mov QWORD PTR [r8+640], r14",
        "mov QWORD PTR [r8+648], r15",
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
        "mov BYTE PTR [r15+r14*1+656], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+720], cl",
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
        "mov BYTE PTR [r15+r14*1+656], al",
        "mov BYTE PTR [r15+r14*1+720], cl",
        "add r14, 1",
        "cmp r14, 64",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rdi, rbx",
        "call {vg_sha256_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 656",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha256_update_avx2}",
        "mov rdi, r12",
        "call {vg_sha256_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 720",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha256_update_avx2}",
        "mov rbx, QWORD PTR [r15+608]",
        "mov rbp, QWORD PTR [r15+616]",
        "mov r12, QWORD PTR [r15+624]",
        "mov r13, QWORD PTR [r15+632]",
        "mov r14, QWORD PTR [r15+640]",
        "mov r15, QWORD PTR [r15+648]",
        "ret",
        vg_sha256_init = sym super::sha256::vg_sha256_init,
        vg_sha256_update_avx2 = sym super::sha256::vg_sha256_update_avx2,
    )
}

/// The CPU features `vg_hmac_sha256_finalize_avx2` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA256_FINALIZE_AVX2_FEATURES: &[&str] = &["avx", "avx2", "bmi1", "bmi2"];

/// Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text of fewer than 2⁶⁴ − 64 bytes, the SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the text under `K₀` (32 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha256I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 96 bytes.
/// * `outer` must be valid for reads of 96 bytes.
/// * `out` must be valid for reads and writes of 32 bytes.
/// * `scratch` must be valid for reads and writes of 832 bytes.
/// * The contents of `inner` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `avx`, `avx2`, `bmi1` and `bmi2` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_finalize_avx2(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+608], rbx",
        "mov QWORD PTR [r8+616], rbp",
        "mov QWORD PTR [r8+624], r12",
        "mov QWORD PTR [r8+632], r13",
        "mov QWORD PTR [r8+640], r14",
        "mov QWORD PTR [r8+648], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 656",
        "mov rcx, r15",
        "call {vg_sha256_finalize_avx2}",
        "mov eax, DWORD PTR [r12]",
        "mov DWORD PTR [rbx], eax",
        "mov eax, DWORD PTR [r12+4]",
        "mov DWORD PTR [rbx+4], eax",
        "mov eax, DWORD PTR [r12+8]",
        "mov DWORD PTR [rbx+8], eax",
        "mov eax, DWORD PTR [r12+12]",
        "mov DWORD PTR [rbx+12], eax",
        "mov eax, DWORD PTR [r12+16]",
        "mov DWORD PTR [rbx+16], eax",
        "mov eax, DWORD PTR [r12+20]",
        "mov DWORD PTR [rbx+20], eax",
        "mov eax, DWORD PTR [r12+24]",
        "mov DWORD PTR [rbx+24], eax",
        "mov eax, DWORD PTR [r12+28]",
        "mov DWORD PTR [rbx+28], eax",
        "mov eax, DWORD PTR [r15+656]",
        "mov DWORD PTR [rbx+32], eax",
        "mov eax, DWORD PTR [r15+660]",
        "mov DWORD PTR [rbx+36], eax",
        "mov eax, DWORD PTR [r15+664]",
        "mov DWORD PTR [rbx+40], eax",
        "mov eax, DWORD PTR [r15+668]",
        "mov DWORD PTR [rbx+44], eax",
        "mov eax, DWORD PTR [r15+672]",
        "mov DWORD PTR [rbx+48], eax",
        "mov eax, DWORD PTR [r15+676]",
        "mov DWORD PTR [rbx+52], eax",
        "mov eax, DWORD PTR [r15+680]",
        "mov DWORD PTR [rbx+56], eax",
        "mov eax, DWORD PTR [r15+684]",
        "mov DWORD PTR [rbx+60], eax",
        "mov rbp, rbx",
        "add rbp, 32",
        "mov eax, 128",
        "mov DWORD PTR [rbp+32], eax",
        "mov eax, 0",
        "mov DWORD PTR [rbp+36], eax",
        "mov DWORD PTR [rbp+40], eax",
        "mov DWORD PTR [rbp+44], eax",
        "mov DWORD PTR [rbp+48], eax",
        "mov DWORD PTR [rbp+52], eax",
        "mov r12d, 96",
        "mov rax, r12",
        "add rax, rax",
        "add rax, rax",
        "add rax, rax",
        "bswap rax",
        "mov QWORD PTR [rbx+88], rax",
        "mov rsi, rbp",
        "mov rdi, rbx",
        "mov edx, 1",
        "mov rcx, r15",
        "call {vg_sha256_compress_avx2}",
        "mov rbx, rdi",
        "mov r15, rcx",
        "mov rbp, r13",
        "mov eax, DWORD PTR [rbx]",
        "bswap eax",
        "mov DWORD PTR [rbp], eax",
        "mov eax, DWORD PTR [rbx+4]",
        "bswap eax",
        "mov DWORD PTR [rbp+4], eax",
        "mov eax, DWORD PTR [rbx+8]",
        "bswap eax",
        "mov DWORD PTR [rbp+8], eax",
        "mov eax, DWORD PTR [rbx+12]",
        "bswap eax",
        "mov DWORD PTR [rbp+12], eax",
        "mov eax, DWORD PTR [rbx+16]",
        "bswap eax",
        "mov DWORD PTR [rbp+16], eax",
        "mov eax, DWORD PTR [rbx+20]",
        "bswap eax",
        "mov DWORD PTR [rbp+20], eax",
        "mov eax, DWORD PTR [rbx+24]",
        "bswap eax",
        "mov DWORD PTR [rbp+24], eax",
        "mov eax, DWORD PTR [rbx+28]",
        "bswap eax",
        "mov DWORD PTR [rbp+28], eax",
        "mov rbx, QWORD PTR [r15+608]",
        "mov rbp, QWORD PTR [r15+616]",
        "mov r12, QWORD PTR [r15+624]",
        "mov r13, QWORD PTR [r15+632]",
        "mov r14, QWORD PTR [r15+640]",
        "mov r15, QWORD PTR [r15+648]",
        "ret",
        vg_sha256_finalize_avx2 = sym super::sha256::vg_sha256_finalize_avx2,
        vg_sha256_compress_avx2 = sym super::sha256::vg_sha256_compress_avx2,
    )
}

/// The CPU features `vg_hmac_sha256_init_shani` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA256_INIT_SHANI_FEATURES: &[&str] = &["sha", "ssse3"];

/// Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha256I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 96 bytes.
/// * `outer` must be valid for reads and writes of 96 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 832 bytes.
/// * `key_len` must be at most 64.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `sha` and `ssse3` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_init_shani(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+608], rbx",
        "mov QWORD PTR [r8+616], rbp",
        "mov QWORD PTR [r8+624], r12",
        "mov QWORD PTR [r8+632], r13",
        "mov QWORD PTR [r8+640], r14",
        "mov QWORD PTR [r8+648], r15",
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
        "mov BYTE PTR [r15+r14*1+656], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+720], cl",
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
        "mov BYTE PTR [r15+r14*1+656], al",
        "mov BYTE PTR [r15+r14*1+720], cl",
        "add r14, 1",
        "cmp r14, 64",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rdi, rbx",
        "call {vg_sha256_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 656",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha256_update_shani}",
        "mov rdi, r12",
        "call {vg_sha256_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 720",
        "mov ecx, 64",
        "mov r8, r15",
        "call {vg_sha256_update_shani}",
        "mov rbx, QWORD PTR [r15+608]",
        "mov rbp, QWORD PTR [r15+616]",
        "mov r12, QWORD PTR [r15+624]",
        "mov r13, QWORD PTR [r15+632]",
        "mov r14, QWORD PTR [r15+640]",
        "mov r15, QWORD PTR [r15+648]",
        "ret",
        vg_sha256_init = sym super::sha256::vg_sha256_init,
        vg_sha256_update_shani = sym super::sha256::vg_sha256_update_shani,
    )
}

/// The CPU features `vg_hmac_sha256_finalize_shani` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES: &[&str] = &["sha", "ssse3"];

/// Finishes an HMAC-SHA-256 computation: if, for a 64-byte key `K₀` and a text of fewer than 2⁶⁴ − 64 bytes, the SHA-256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the text under `K₀` (32 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha256I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 96 bytes.
/// * `outer` must be valid for reads of 96 bytes.
/// * `out` must be valid for reads and writes of 32 bytes.
/// * `scratch` must be valid for reads and writes of 832 bytes.
/// * The contents of `inner` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `sha` and `ssse3` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_finalize_shani(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+608], rbx",
        "mov QWORD PTR [r8+616], rbp",
        "mov QWORD PTR [r8+624], r12",
        "mov QWORD PTR [r8+632], r13",
        "mov QWORD PTR [r8+640], r14",
        "mov QWORD PTR [r8+648], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 656",
        "mov rcx, r15",
        "call {vg_sha256_finalize_shani}",
        "mov eax, DWORD PTR [r12]",
        "mov DWORD PTR [rbx], eax",
        "mov eax, DWORD PTR [r12+4]",
        "mov DWORD PTR [rbx+4], eax",
        "mov eax, DWORD PTR [r12+8]",
        "mov DWORD PTR [rbx+8], eax",
        "mov eax, DWORD PTR [r12+12]",
        "mov DWORD PTR [rbx+12], eax",
        "mov eax, DWORD PTR [r12+16]",
        "mov DWORD PTR [rbx+16], eax",
        "mov eax, DWORD PTR [r12+20]",
        "mov DWORD PTR [rbx+20], eax",
        "mov eax, DWORD PTR [r12+24]",
        "mov DWORD PTR [rbx+24], eax",
        "mov eax, DWORD PTR [r12+28]",
        "mov DWORD PTR [rbx+28], eax",
        "mov eax, DWORD PTR [r15+656]",
        "mov DWORD PTR [rbx+32], eax",
        "mov eax, DWORD PTR [r15+660]",
        "mov DWORD PTR [rbx+36], eax",
        "mov eax, DWORD PTR [r15+664]",
        "mov DWORD PTR [rbx+40], eax",
        "mov eax, DWORD PTR [r15+668]",
        "mov DWORD PTR [rbx+44], eax",
        "mov eax, DWORD PTR [r15+672]",
        "mov DWORD PTR [rbx+48], eax",
        "mov eax, DWORD PTR [r15+676]",
        "mov DWORD PTR [rbx+52], eax",
        "mov eax, DWORD PTR [r15+680]",
        "mov DWORD PTR [rbx+56], eax",
        "mov eax, DWORD PTR [r15+684]",
        "mov DWORD PTR [rbx+60], eax",
        "mov rbp, rbx",
        "add rbp, 32",
        "mov eax, 128",
        "mov DWORD PTR [rbp+32], eax",
        "mov eax, 0",
        "mov DWORD PTR [rbp+36], eax",
        "mov DWORD PTR [rbp+40], eax",
        "mov DWORD PTR [rbp+44], eax",
        "mov DWORD PTR [rbp+48], eax",
        "mov DWORD PTR [rbp+52], eax",
        "mov r12d, 96",
        "mov rax, r12",
        "add rax, rax",
        "add rax, rax",
        "add rax, rax",
        "bswap rax",
        "mov QWORD PTR [rbx+88], rax",
        "mov rsi, rbp",
        "mov rdi, rbx",
        "mov edx, 1",
        "mov rcx, r15",
        "call {vg_sha256_compress_shani}",
        "mov rbx, rdi",
        "mov r15, rcx",
        "mov rbp, r13",
        "mov eax, DWORD PTR [rbx]",
        "bswap eax",
        "mov DWORD PTR [rbp], eax",
        "mov eax, DWORD PTR [rbx+4]",
        "bswap eax",
        "mov DWORD PTR [rbp+4], eax",
        "mov eax, DWORD PTR [rbx+8]",
        "bswap eax",
        "mov DWORD PTR [rbp+8], eax",
        "mov eax, DWORD PTR [rbx+12]",
        "bswap eax",
        "mov DWORD PTR [rbp+12], eax",
        "mov eax, DWORD PTR [rbx+16]",
        "bswap eax",
        "mov DWORD PTR [rbp+16], eax",
        "mov eax, DWORD PTR [rbx+20]",
        "bswap eax",
        "mov DWORD PTR [rbp+20], eax",
        "mov eax, DWORD PTR [rbx+24]",
        "bswap eax",
        "mov DWORD PTR [rbp+24], eax",
        "mov eax, DWORD PTR [rbx+28]",
        "bswap eax",
        "mov DWORD PTR [rbp+28], eax",
        "mov rbx, QWORD PTR [r15+608]",
        "mov rbp, QWORD PTR [r15+616]",
        "mov r12, QWORD PTR [r15+624]",
        "mov r13, QWORD PTR [r15+632]",
        "mov r14, QWORD PTR [r15+640]",
        "mov r15, QWORD PTR [r15+648]",
        "ret",
        vg_sha256_finalize_shani = sym super::sha256::vg_sha256_finalize_shani,
        vg_sha256_compress_shani = sym super::sha256::vg_sha256_compress_shani,
    )
}
