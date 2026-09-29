// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem` functions for `arm`.
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
/// * Neither `f` nor `g` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_add(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "mov r2, #256",
        "20:",
        "ldr r3, [r0, #0]",
        "ldr r12, [r1, #0]",
        "add r3, r3, r12",
        "sub r3, r3, #3328",
        "sub r3, r3, #1",
        "lsr r12, r3, #31",
        "add r3, r3, r12",
        "add r3, r3, r12, lsl #8",
        "add r3, r3, r12, lsl #10",
        "add r3, r3, r12, lsl #11",
        "str r3, [r0, #0]",
        "add r0, r0, #4",
        "add r1, r1, #4",
        "subs r2, r2, #1",
        "bne 20b",
        "bx lr",
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
/// * Neither `f` nor `g` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_sub(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "mov r2, #256",
        "20:",
        "ldr r3, [r0, #0]",
        "ldr r12, [r1, #0]",
        "sub r3, r3, r12",
        "lsr r12, r3, #31",
        "add r3, r3, r12",
        "add r3, r3, r12, lsl #8",
        "add r3, r3, r12, lsl #10",
        "add r3, r3, r12, lsl #11",
        "str r3, [r0, #0]",
        "add r0, r0, #4",
        "add r1, r1, #4",
        "subs r2, r2, #1",
        "bne 20b",
        "bx lr",
    )
}
