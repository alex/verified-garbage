// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `hmac_sha384` functions for `x86_64`.
#![allow(dead_code)]

/// The CPU features `vg_hmac_sha384_init_avx2` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA384_INIT_AVX2_FEATURES: &[&str] = &["avx", "avx2", "bmi1", "bmi2"];

/// Starts an HMAC-SHA-384 computation with a key of at most 128 bytes: makes the SHA-384 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 128 bytes (FIPS 198-1). The text is then absorbed with `vg_sha512_update` on `*inner` (its `count` starting at 128), and the MAC computed with `vg_hmac_sha384_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha384I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 192 bytes.
/// * `outer` must be valid for reads and writes of 192 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 1872 bytes.
/// * `key_len` must be at most 128.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `avx`, `avx2`, `bmi1` and `bmi2` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha384_init_avx2(inner: *mut [u8; 192], outer: *mut [u8; 192], key: *const u8, key_len: usize, scratch: *mut [u64; 234]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+1376], rbx",
        "mov QWORD PTR [r8+1384], rbp",
        "mov QWORD PTR [r8+1392], r12",
        "mov QWORD PTR [r8+1400], r13",
        "mov QWORD PTR [r8+1408], r14",
        "mov QWORD PTR [r8+1416], r15",
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
        "mov BYTE PTR [r15+r14*1+1424], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+1552], cl",
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
        "mov BYTE PTR [r15+r14*1+1424], al",
        "mov BYTE PTR [r15+r14*1+1552], cl",
        "add r14, 1",
        "cmp r14, 128",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rdi, rbx",
        "call {vg_sha384_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 1424",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update_avx2}",
        "mov rdi, r12",
        "call {vg_sha384_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 1552",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update_avx2}",
        "mov rbx, QWORD PTR [r15+1376]",
        "mov rbp, QWORD PTR [r15+1384]",
        "mov r12, QWORD PTR [r15+1392]",
        "mov r13, QWORD PTR [r15+1400]",
        "mov r14, QWORD PTR [r15+1408]",
        "mov r15, QWORD PTR [r15+1416]",
        "ret",
        vg_sha384_init = sym super::sha512::vg_sha384_init,
        vg_sha512_update_avx2 = sym super::sha512::vg_sha512_update_avx2,
    )
}

/// The CPU features `vg_hmac_sha384_finalize_avx2` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA384_FINALIZE_AVX2_FEATURES: &[&str] = &["avx", "avx2", "bmi1", "bmi2"];

/// Finishes an HMAC-SHA-384 computation: if, for a 128-byte key `K₀` and a text of fewer than 2⁶⁴ − 128 bytes, the SHA-384 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-384 of the text under `K₀` (48 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha384I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 192 bytes.
/// * `outer` must be valid for reads of 192 bytes.
/// * `out` must be valid for reads and writes of 48 bytes.
/// * `scratch` must be valid for reads and writes of 1872 bytes.
/// * The contents of `inner` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `avx`, `avx2`, `bmi1` and `bmi2` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha384_finalize_avx2(inner: *mut [u8; 192], outer: *const [u8; 192], count: u64, out: *mut [u8; 48], scratch: *mut [u64; 234]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+1376], rbx",
        "mov QWORD PTR [r8+1384], rbp",
        "mov QWORD PTR [r8+1392], r12",
        "mov QWORD PTR [r8+1400], r13",
        "mov QWORD PTR [r8+1408], r14",
        "mov QWORD PTR [r8+1416], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 1424",
        "mov rcx, r15",
        "call {vg_sha512_finalize_avx2}",
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
        "add rdx, 1424",
        "mov ecx, 48",
        "mov r8, r15",
        "call {vg_sha512_update_avx2}",
        "mov rdi, rbx",
        "mov esi, 176",
        "mov rdx, r15",
        "add rdx, 1424",
        "mov rcx, r15",
        "call {vg_sha512_finalize_avx2}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+1424]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 48",
        "jne 21b",
        "mov rbx, QWORD PTR [r15+1376]",
        "mov rbp, QWORD PTR [r15+1384]",
        "mov r12, QWORD PTR [r15+1392]",
        "mov r13, QWORD PTR [r15+1400]",
        "mov r14, QWORD PTR [r15+1408]",
        "mov r15, QWORD PTR [r15+1416]",
        "ret",
        vg_sha512_finalize_avx2 = sym super::sha512::vg_sha512_finalize_avx2,
        vg_sha512_update_avx2 = sym super::sha512::vg_sha512_update_avx2,
    )
}

/// Starts an HMAC-SHA-384 computation with a key of at most 128 bytes: makes the SHA-384 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 128 bytes (FIPS 198-1). The text is then absorbed with `vg_sha512_update` on `*inner` (its `count` starting at 128), and the MAC computed with `vg_hmac_sha384_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha384I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 192 bytes.
/// * `outer` must be valid for reads and writes of 192 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 1872 bytes.
/// * `key_len` must be at most 128.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha384_init(inner: *mut [u8; 192], outer: *mut [u8; 192], key: *const u8, key_len: usize, scratch: *mut [u64; 234]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+1376], rbx",
        "mov QWORD PTR [r8+1384], rbp",
        "mov QWORD PTR [r8+1392], r12",
        "mov QWORD PTR [r8+1400], r13",
        "mov QWORD PTR [r8+1408], r14",
        "mov QWORD PTR [r8+1416], r15",
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
        "mov BYTE PTR [r15+r14*1+1424], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+1552], cl",
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
        "mov BYTE PTR [r15+r14*1+1424], al",
        "mov BYTE PTR [r15+r14*1+1552], cl",
        "add r14, 1",
        "cmp r14, 128",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rdi, rbx",
        "call {vg_sha384_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 1424",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, r12",
        "call {vg_sha384_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 1552",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rbx, QWORD PTR [r15+1376]",
        "mov rbp, QWORD PTR [r15+1384]",
        "mov r12, QWORD PTR [r15+1392]",
        "mov r13, QWORD PTR [r15+1400]",
        "mov r14, QWORD PTR [r15+1408]",
        "mov r15, QWORD PTR [r15+1416]",
        "ret",
        vg_sha384_init = sym super::sha512::vg_sha384_init,
        vg_sha512_update = sym super::sha512::vg_sha512_update,
    )
}

/// Finishes an HMAC-SHA-384 computation: if, for a 128-byte key `K₀` and a text of fewer than 2⁶⁴ − 128 bytes, the SHA-384 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-384 of the text under `K₀` (48 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha384I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 192 bytes.
/// * `outer` must be valid for reads of 192 bytes.
/// * `out` must be valid for reads and writes of 48 bytes.
/// * `scratch` must be valid for reads and writes of 1872 bytes.
/// * The contents of `inner` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha384_finalize(inner: *mut [u8; 192], outer: *const [u8; 192], count: u64, out: *mut [u8; 48], scratch: *mut [u64; 234]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+1376], rbx",
        "mov QWORD PTR [r8+1384], rbp",
        "mov QWORD PTR [r8+1392], r12",
        "mov QWORD PTR [r8+1400], r13",
        "mov QWORD PTR [r8+1408], r14",
        "mov QWORD PTR [r8+1416], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 1424",
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
        "add rdx, 1424",
        "mov ecx, 48",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, rbx",
        "mov esi, 176",
        "mov rdx, r15",
        "add rdx, 1424",
        "mov rcx, r15",
        "call {vg_sha512_finalize}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+1424]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 48",
        "jne 21b",
        "mov rbx, QWORD PTR [r15+1376]",
        "mov rbp, QWORD PTR [r15+1384]",
        "mov r12, QWORD PTR [r15+1392]",
        "mov r13, QWORD PTR [r15+1400]",
        "mov r14, QWORD PTR [r15+1408]",
        "mov r15, QWORD PTR [r15+1416]",
        "ret",
        vg_sha512_finalize = sym super::sha512::vg_sha512_finalize,
        vg_sha512_update = sym super::sha512::vg_sha512_update,
    )
}

/// The CPU features `vg_hmac_sha384_init_shani` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA384_INIT_SHANI_FEATURES: &[&str] = &["avx", "avx2", "sha512"];

/// Starts an HMAC-SHA-384 computation with a key of at most 128 bytes: makes the SHA-384 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 128 bytes (FIPS 198-1). The text is then absorbed with `vg_sha512_update` on `*inner` (its `count` starting at 128), and the MAC computed with `vg_hmac_sha384_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha384I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 192 bytes.
/// * `outer` must be valid for reads and writes of 192 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 1872 bytes.
/// * `key_len` must be at most 128.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `avx`, `avx2` and `sha512` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha384_init_shani(inner: *mut [u8; 192], outer: *mut [u8; 192], key: *const u8, key_len: usize, scratch: *mut [u64; 234]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+1376], rbx",
        "mov QWORD PTR [r8+1384], rbp",
        "mov QWORD PTR [r8+1392], r12",
        "mov QWORD PTR [r8+1400], r13",
        "mov QWORD PTR [r8+1408], r14",
        "mov QWORD PTR [r8+1416], r15",
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
        "mov BYTE PTR [r15+r14*1+1424], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+1552], cl",
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
        "mov BYTE PTR [r15+r14*1+1424], al",
        "mov BYTE PTR [r15+r14*1+1552], cl",
        "add r14, 1",
        "cmp r14, 128",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
        "mov rdi, rbx",
        "call {vg_sha384_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 1424",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update_shani}",
        "mov rdi, r12",
        "call {vg_sha384_init}",
        "mov rdi, r12",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 1552",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update_shani}",
        "mov rbx, QWORD PTR [r15+1376]",
        "mov rbp, QWORD PTR [r15+1384]",
        "mov r12, QWORD PTR [r15+1392]",
        "mov r13, QWORD PTR [r15+1400]",
        "mov r14, QWORD PTR [r15+1408]",
        "mov r15, QWORD PTR [r15+1416]",
        "ret",
        vg_sha384_init = sym super::sha512::vg_sha384_init,
        vg_sha512_update_shani = sym super::sha512::vg_sha512_update_shani,
    )
}

/// The CPU features `vg_hmac_sha384_finalize_shani` requires (`Artifact.features`).
pub(crate) const VG_HMAC_SHA384_FINALIZE_SHANI_FEATURES: &[&str] = &["avx", "avx2", "sha512"];

/// Finishes an HMAC-SHA-384 computation: if, for a 128-byte key `K₀` and a text of fewer than 2⁶⁴ − 128 bytes, the SHA-384 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-384 of the text under `K₀` (48 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha384I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 192 bytes.
/// * `outer` must be valid for reads of 192 bytes.
/// * `out` must be valid for reads and writes of 48 bytes.
/// * `scratch` must be valid for reads and writes of 1872 bytes.
/// * The contents of `inner` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
/// * The CPU must support the `avx`, `avx2` and `sha512` target features.
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha384_finalize_shani(inner: *mut [u8; 192], outer: *const [u8; 192], count: u64, out: *mut [u8; 48], scratch: *mut [u64; 234]) {
    core::arch::naked_asm!(
        "mov QWORD PTR [r8+1376], rbx",
        "mov QWORD PTR [r8+1384], rbp",
        "mov QWORD PTR [r8+1392], r12",
        "mov QWORD PTR [r8+1400], r13",
        "mov QWORD PTR [r8+1408], r14",
        "mov QWORD PTR [r8+1416], r15",
        "mov rbx, rdi",
        "mov r12, rsi",
        "mov r13, rcx",
        "mov r15, r8",
        "mov rsi, rdx",
        "mov rdx, r15",
        "add rdx, 1424",
        "mov rcx, r15",
        "call {vg_sha512_finalize_shani}",
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
        "add rdx, 1424",
        "mov ecx, 48",
        "mov r8, r15",
        "call {vg_sha512_update_shani}",
        "mov rdi, rbx",
        "mov esi, 176",
        "mov rdx, r15",
        "add rdx, 1424",
        "mov rcx, r15",
        "call {vg_sha512_finalize_shani}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+1424]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 48",
        "jne 21b",
        "mov rbx, QWORD PTR [r15+1376]",
        "mov rbp, QWORD PTR [r15+1384]",
        "mov r12, QWORD PTR [r15+1392]",
        "mov r13, QWORD PTR [r15+1400]",
        "mov r14, QWORD PTR [r15+1408]",
        "mov r15, QWORD PTR [r15+1416]",
        "ret",
        vg_sha512_finalize_shani = sym super::sha512::vg_sha512_finalize_shani,
        vg_sha512_update_shani = sym super::sha512::vg_sha512_update_shani,
    )
}
