// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem768` functions for `aarch64`.
#![allow(dead_code)]

/// The ML-KEM-768 encapsulation key check (FIPS 203 §7.2): returns 1 if every 12-bit integer that the first 1152 bytes of `*ek` encode is less than `q` = 3329 (the modulus check), and 0 otherwise. An encapsulation key must pass it before it is given to `vg_mlkem768_encaps`.
///
/// Contract: `VG.Spec.MlKem.checkEkContract`. Constant time: only the pointer may affect timing.
///
/// # Safety
///
/// * `ek` must be valid for reads of 1184 bytes.
/// * `ek` must not wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem768_check_ek(ek: *const [u8; 1184]) -> u32 {
    core::arch::naked_asm!(
        "movz x9, #3328, lsl #0",
        "movz x10, #0, lsl #0",
        "movz x11, #384, lsl #0",
        "movz x14, #15, lsl #0",
        "20:",
        "ldrb w12, [x0, #0]",
        "ldrb w13, [x0, #1]",
        "and x15, x13, x14",
        "lsl x15, x15, #8",
        "add x15, x15, x12",
        "sub x15, x9, x15",
        "lsr x15, x15, #63",
        "add x10, x10, x15",
        "ldrb w12, [x0, #2]",
        "lsr x13, x13, #4",
        "lsl x12, x12, #4",
        "add x13, x13, x12",
        "sub x13, x9, x13",
        "lsr x13, x13, #63",
        "add x10, x10, x13",
        "add x0, x0, #3",
        "sub x11, x11, #1",
        "cbnz x11, 20b",
        "sub x0, x10, #1",
        "lsr x0, x0, #63",
        "ret",
    )
}
