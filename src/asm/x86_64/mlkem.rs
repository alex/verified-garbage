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
