// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem` functions for `aarch64`.
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
        "movz x9, #3329, lsl #0",
        "movz x10, #256, lsl #0",
        "20:",
        "ldr w11, [x0, #0]",
        "ldr w12, [x1, #0]",
        "add x11, x11, x12",
        "sub x11, x11, x9",
        "lsr x13, x11, #63",
        "madd x11, x13, x9, x11",
        "str w11, [x0, #0]",
        "add x0, x0, #4",
        "add x1, x1, #4",
        "sub x10, x10, #1",
        "cbnz x10, 20b",
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
/// * Neither `f` nor `g` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_sub(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "movz x9, #3329, lsl #0",
        "movz x10, #256, lsl #0",
        "20:",
        "ldr w11, [x0, #0]",
        "ldr w12, [x1, #0]",
        "add x11, x11, x9",
        "sub x11, x11, x12",
        "sub x11, x11, x9",
        "lsr x13, x11, #63",
        "madd x11, x13, x9, x11",
        "str w11, [x0, #0]",
        "add x0, x0, #4",
        "add x1, x1, #4",
        "sub x10, x10, #1",
        "cbnz x10, 20b",
        "ret",
    )
}
