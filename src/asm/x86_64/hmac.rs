// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `hmac` functions for `x86_64`.
#![allow(dead_code)]

/// Starts an HMAC-SHA-1 computation with a key of at most 64 bytes: makes the SHA-1 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_sha1_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_sha1_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha1I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `key_len` must be at most 64.
/// * `inner` and `outer` must each be valid for reads and writes of 84 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 448 bytes; its contents on return are unspecified.
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
/// * `inner` must be valid for reads and writes of 84 bytes; its contents on return are unspecified.
/// * `outer` must be valid for reads of 84 bytes.
/// * `out` must be valid for writes of 20 bytes.
/// * `scratch` must be valid for reads and writes of 448 bytes; its contents on return are unspecified.
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

/// Starts an HMAC-MD5 computation with a key of at most 64 bytes: makes the MD5 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_md5_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_md5_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.md5I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `key_len` must be at most 64.
/// * `inner` and `outer` must each be valid for reads and writes of 80 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 384 bytes; its contents on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_md5_init(inner: *mut [u8; 80], outer: *mut [u8; 80], key: *const u8, key_len: usize, scratch: *mut [u64; 48]) {
    core::arch::naked_asm!(
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
        "je 20f",
        "22:",
        "movzx eax, BYTE PTR [rbp+r14*1]",
        "mov ecx, eax",
        "xor eax, 54",
        "mov BYTE PTR [r15+r14*1+160], al",
        "xor ecx, 92",
        "mov BYTE PTR [r15+r14*1+224], cl",
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
        "mov BYTE PTR [r15+r14*1+160], al",
        "mov BYTE PTR [r15+r14*1+224], cl",
        "add r14, 1",
        "cmp r14, 64",
        "jne 25b",
        "jmp 24f",
        "23:",
        "24:",
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
    )
}

/// Finishes an HMAC-MD5 computation: if, for a 64-byte key `K₀` and a text of fewer than 2⁶⁴ − 64 bytes, the MD5 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-MD5 of the text under `K₀` (16 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.md5I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 80 bytes; its contents on return are unspecified.
/// * `outer` must be valid for reads of 80 bytes.
/// * `out` must be valid for writes of 16 bytes.
/// * `scratch` must be valid for reads and writes of 384 bytes; its contents on return are unspecified.
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
        "mov r14d, 0",
        "20:",
        "movzx eax, BYTE PTR [r12+r14*1]",
        "mov BYTE PTR [rbx+r14*1], al",
        "add r14, 1",
        "cmp r14, 80",
        "jne 20b",
        "mov rdi, rbx",
        "mov esi, 64",
        "mov rdx, r15",
        "add rdx, 160",
        "mov ecx, 16",
        "mov r8, r15",
        "call {vg_md5_update}",
        "mov rdi, rbx",
        "mov esi, 80",
        "mov rdx, r15",
        "add rdx, 160",
        "mov rcx, r15",
        "call {vg_md5_finalize}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+160]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 16",
        "jne 21b",
        "mov rbx, QWORD PTR [r15+112]",
        "mov rbp, QWORD PTR [r15+120]",
        "mov r12, QWORD PTR [r15+128]",
        "mov r13, QWORD PTR [r15+136]",
        "mov r14, QWORD PTR [r15+144]",
        "mov r15, QWORD PTR [r15+152]",
        "ret",
        vg_md5_finalize = sym super::md5::vg_md5_finalize,
        vg_md5_update = sym super::md5::vg_md5_update,
    )
}

/// Starts an HMAC-SHA-384 computation with a key of at most 128 bytes: makes the SHA-384 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 128 bytes (FIPS 198-1). The text is then absorbed with `vg_sha512_update` on `*inner` (its `count` starting at 128), and the MAC computed with `vg_hmac_sha384_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha384I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
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
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha384_init(inner: *mut [u8; 192], outer: *mut [u8; 192], key: *const u8, key_len: usize, scratch: *mut [u64; 96]) {
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
        "call {vg_sha384_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 320",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, r12",
        "call {vg_sha384_init}",
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
/// * `inner` must be valid for reads and writes of 192 bytes; its contents on return are unspecified.
/// * `outer` must be valid for reads of 192 bytes.
/// * `out` must be valid for writes of 48 bytes.
/// * `scratch` must be valid for reads and writes of 768 bytes; its contents on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha384_finalize(inner: *mut [u8; 192], outer: *const [u8; 192], count: u64, out: *mut [u8; 48], scratch: *mut [u64; 96]) {
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
        "mov ecx, 48",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, rbx",
        "mov esi, 176",
        "mov rdx, r15",
        "add rdx, 320",
        "mov rcx, r15",
        "call {vg_sha512_finalize}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+320]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 48",
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

/// Starts an HMAC-SHA-512/224 computation with a key of at most 128 bytes: makes the SHA-512/224 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 128 bytes (FIPS 198-1). The text is then absorbed with `vg_sha512_update` on `*inner` (its `count` starting at 128), and the MAC computed with `vg_hmac_sha512_224_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha512_224I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
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
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha512_224_init(inner: *mut [u8; 192], outer: *mut [u8; 192], key: *const u8, key_len: usize, scratch: *mut [u64; 96]) {
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
        "call {vg_sha512_224_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 320",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, r12",
        "call {vg_sha512_224_init}",
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
        vg_sha512_224_init = sym super::sha512::vg_sha512_224_init,
        vg_sha512_update = sym super::sha512::vg_sha512_update,
    )
}

/// Finishes an HMAC-SHA-512/224 computation: if, for a 128-byte key `K₀` and a text of fewer than 2⁶⁴ − 128 bytes, the SHA-512/224 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-512/224 of the text under `K₀` (28 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha512_224I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 192 bytes; its contents on return are unspecified.
/// * `outer` must be valid for reads of 192 bytes.
/// * `out` must be valid for writes of 28 bytes.
/// * `scratch` must be valid for reads and writes of 768 bytes; its contents on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha512_224_finalize(inner: *mut [u8; 192], outer: *const [u8; 192], count: u64, out: *mut [u8; 28], scratch: *mut [u64; 96]) {
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
        "mov ecx, 28",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, rbx",
        "mov esi, 156",
        "mov rdx, r15",
        "add rdx, 320",
        "mov rcx, r15",
        "call {vg_sha512_finalize}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+320]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 28",
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

/// Starts an HMAC-SHA-512/256 computation with a key of at most 128 bytes: makes the SHA-512/256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 128 bytes (FIPS 198-1). The text is then absorbed with `vg_sha512_update` on `*inner` (its `count` starting at 128), and the MAC computed with `vg_hmac_sha512_256_finalize`.
///
/// Contract: `VG.Spec.Hmac.Instance.initContract` of `VG.Spec.Hmac.sha512_256I`. Constant time: only the pointers and `key_len` may affect timing, not the key.
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
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha512_256_init(inner: *mut [u8; 192], outer: *mut [u8; 192], key: *const u8, key_len: usize, scratch: *mut [u64; 96]) {
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
        "call {vg_sha512_256_init}",
        "mov rdi, rbx",
        "mov esi, 0",
        "mov rdx, r15",
        "add rdx, 320",
        "mov ecx, 128",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, r12",
        "call {vg_sha512_256_init}",
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
        vg_sha512_256_init = sym super::sha512::vg_sha512_256_init,
        vg_sha512_update = sym super::sha512::vg_sha512_update,
    )
}

/// Finishes an HMAC-SHA-512/256 computation: if, for a 128-byte key `K₀` and a text of fewer than 2⁶⁴ − 128 bytes, the SHA-512/256 streaming state `*inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-512/256 of the text under `K₀` (32 bytes) to `*out`.
///
/// Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.sha512_256I`. Constant time: only the pointers and `count` may affect timing, not the states.
///
/// # Safety
///
/// * `inner` must be valid for reads and writes of 192 bytes; its contents on return are unspecified.
/// * `outer` must be valid for reads of 192 bytes.
/// * `out` must be valid for writes of 32 bytes.
/// * `scratch` must be valid for reads and writes of 768 bytes; its contents on return are unspecified.
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha512_256_finalize(inner: *mut [u8; 192], outer: *const [u8; 192], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 96]) {
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
        "mov ecx, 32",
        "mov r8, r15",
        "call {vg_sha512_update}",
        "mov rdi, rbx",
        "mov esi, 160",
        "mov rdx, r15",
        "add rdx, 320",
        "mov rcx, r15",
        "call {vg_sha512_finalize}",
        "mov r14d, 0",
        "21:",
        "movzx eax, BYTE PTR [r15+r14*1+320]",
        "mov BYTE PTR [r13+r14*1], al",
        "add r14, 1",
        "cmp r14, 32",
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

/// Starts an HMAC-SHA-256 computation with a key of at most 64 bytes: makes the SHA-256 streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where `K₀` is the `key_len` bytes at `key` padded with zeros to 64 bytes (FIPS 198-1). The text is then absorbed with `vg_sha256_update` on `*inner` (its `count` starting at 64), and the MAC computed with `vg_hmac_sha256_finalize`.
///
/// Contract: `VG.Spec.Hmac.initSha256Contract`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// # Safety
///
/// * `key_len` must be at most 64.
/// * `inner` and `outer` must each be valid for reads and writes of 96 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 160 bytes; its contents on return are unspecified.
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the return address on the stack or the 8 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20]) {
    core::arch::naked_asm!(
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
        "mov rbx, QWORD PTR [r15+112]",
        "mov rbp, QWORD PTR [r15+120]",
        "mov r12, QWORD PTR [r15+128]",
        "mov r13, QWORD PTR [r15+136]",
        "mov r14, QWORD PTR [r15+144]",
        "mov r15, QWORD PTR [r15+152]",
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
/// * `scratch` must be valid for reads and writes of 240 bytes; its contents on return are unspecified, apart from the MAC.
/// * `inner` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer` and `scratch` may overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, scratch: *mut [u64; 30]) {
    core::arch::naked_asm!(
        "mov eax, DWORD PTR [rsi]",
        "mov DWORD PTR [rcx+208], eax",
        "mov eax, DWORD PTR [rsi+4]",
        "mov DWORD PTR [rcx+212], eax",
        "mov eax, DWORD PTR [rsi+8]",
        "mov DWORD PTR [rcx+216], eax",
        "mov eax, DWORD PTR [rsi+12]",
        "mov DWORD PTR [rcx+220], eax",
        "mov eax, DWORD PTR [rsi+16]",
        "mov DWORD PTR [rcx+224], eax",
        "mov eax, DWORD PTR [rsi+20]",
        "mov DWORD PTR [rcx+228], eax",
        "mov eax, DWORD PTR [rsi+24]",
        "mov DWORD PTR [rcx+232], eax",
        "mov eax, DWORD PTR [rsi+28]",
        "mov DWORD PTR [rcx+236], eax",
        "mov rsi, rdx",
        "mov rdx, rcx",
        "add rdx, 176",
        "call {vg_sha256_finalize}",
        "mov eax, DWORD PTR [rcx+208]",
        "mov DWORD PTR [rdi], eax",
        "mov eax, DWORD PTR [rcx+212]",
        "mov DWORD PTR [rdi+4], eax",
        "mov eax, DWORD PTR [rcx+216]",
        "mov DWORD PTR [rdi+8], eax",
        "mov eax, DWORD PTR [rcx+220]",
        "mov DWORD PTR [rdi+12], eax",
        "mov eax, DWORD PTR [rcx+224]",
        "mov DWORD PTR [rdi+16], eax",
        "mov eax, DWORD PTR [rcx+228]",
        "mov DWORD PTR [rdi+20], eax",
        "mov eax, DWORD PTR [rcx+232]",
        "mov DWORD PTR [rdi+24], eax",
        "mov eax, DWORD PTR [rcx+236]",
        "mov DWORD PTR [rdi+28], eax",
        "mov rax, QWORD PTR [rcx+176]",
        "mov QWORD PTR [rdi+32], rax",
        "mov rax, QWORD PTR [rcx+184]",
        "mov QWORD PTR [rdi+40], rax",
        "mov rax, QWORD PTR [rcx+192]",
        "mov QWORD PTR [rdi+48], rax",
        "mov rax, QWORD PTR [rcx+200]",
        "mov QWORD PTR [rdi+56], rax",
        "mov esi, 96",
        "mov rdx, rcx",
        "add rdx, 176",
        "call {vg_sha256_finalize}",
        "ret",
        vg_sha256_finalize = sym super::sha256::vg_sha256_finalize,
    )
}
