// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem` functions for `x86_64`.
#![allow(dead_code)]

/// Adds the polynomial `*g` to `*f` modulo `q` = 3329, coefficient by coefficient (FIPS 203 (2.3)).
///
/// Contract: `VG.Spec.MlKem.addContract`. Constant time: only the pointers may affect timing, not the data.
///
/// # Safety
///
/// * `f` must be valid for reads and writes of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `g` must be valid for reads of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `f` must not overlap `g` (distinct Rust objects never do).
/// * Neither `f` nor `g` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_add(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "mov ecx, 256",
        "20:",
        "mov eax, DWORD PTR [rdi]",
        "add eax, DWORD PTR [rsi]",
        "sub eax, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add eax, edx",
        "mov DWORD PTR [rdi], eax",
        "add rdi, 4",
        "add rsi, 4",
        "sub rcx, 1",
        "jne 20b",
        "ret",
    )
}

/// Subtracts the polynomial `*g` from `*f` modulo `q` = 3329, coefficient by coefficient.
///
/// Contract: `VG.Spec.MlKem.subContract`. Constant time: only the pointers may affect timing, not the data.
///
/// # Safety
///
/// * `f` must be valid for reads and writes of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `g` must be valid for reads of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `f` must not overlap `g` (distinct Rust objects never do).
/// * Neither `f` nor `g` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_sub(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "mov ecx, 256",
        "20:",
        "mov eax, DWORD PTR [rdi]",
        "add eax, 3329",
        "sub eax, DWORD PTR [rsi]",
        "sub eax, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add eax, edx",
        "mov DWORD PTR [rdi], eax",
        "add rdi, 4",
        "add rsi, 4",
        "sub rcx, 1",
        "jne 20b",
        "ret",
    )
}

/// `ByteEncode₁₂` (FIPS 203 Algorithm 5): writes the 256 coefficients of `*f`, each less than `q` = 3329, to `*out` as 12-bit little-endian fields.
///
/// Contract: `VG.Spec.MlKem.encode12Contract`. Constant time: only the pointers may affect timing, not the data.
///
/// # Safety
///
/// * `f` must be valid for reads of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `out` must be valid for writes of 384 bytes.
/// * `out` must not overlap `f` (distinct Rust objects never do).
/// * Neither `f` nor `out` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_encode12(f: *const [u32; 256], out: *mut [u8; 384]) {
    core::arch::naked_asm!(
        "mov ecx, 128",
        "20:",
        "mov eax, DWORD PTR [rdi]",
        "mov edx, DWORD PTR [rdi+4]",
        "ror edx, 20",
        "add eax, edx",
        "mov BYTE PTR [rsi], al",
        "shr eax, 8",
        "mov BYTE PTR [rsi+1], al",
        "shr eax, 8",
        "mov BYTE PTR [rsi+2], al",
        "add rdi, 8",
        "add rsi, 3",
        "sub rcx, 1",
        "jne 20b",
        "ret",
    )
}

/// `ByteDecode₁₂` (FIPS 203 Algorithm 6): writes the 256 12-bit little-endian fields of `*b`, each reduced modulo `q` = 3329, to `*f`.
///
/// Contract: `VG.Spec.MlKem.decode12Contract`. Constant time: only the pointers may affect timing, not the data.
///
/// # Safety
///
/// * `b` must be valid for reads of 384 bytes.
/// * `f` must be valid for writes of 1024 bytes.
/// * `f` must not overlap `b` (distinct Rust objects never do).
/// * Neither `b` nor `f` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_decode12(b: *const [u8; 384], f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov ecx, 128",
        "20:",
        "movzx eax, BYTE PTR [rdi]",
        "movzx edx, BYTE PTR [rdi+1]",
        "ror edx, 24",
        "add eax, edx",
        "movzx edx, BYTE PTR [rdi+2]",
        "ror edx, 16",
        "add eax, edx",
        "mov edx, eax",
        "and eax, 4095",
        "shr edx, 12",
        "sub eax, 3329",
        "sbb r8d, r8d",
        "and r8d, 3329",
        "add eax, r8d",
        "sub edx, 3329",
        "sbb r8d, r8d",
        "and r8d, 3329",
        "add edx, r8d",
        "mov DWORD PTR [rsi], eax",
        "mov DWORD PTR [rsi+4], edx",
        "add rdi, 3",
        "add rsi, 8",
        "sub rcx, 1",
        "jne 20b",
        "ret",
    )
}
