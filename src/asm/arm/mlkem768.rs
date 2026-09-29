// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem768` functions for `arm`.
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
        "mov r1, #384",
        "mov r2, #0",
        "20:",
        "ldrb r3, [r0, #1]",
        "lsl r3, r3, #28",
        "lsr r3, r3, #20",
        "ldrb r12, [r0, #0]",
        "add r3, r3, r12",
        "mov r12, #3328",
        "sub r12, r12, r3",
        "add r2, r2, r12, lsr #31",
        "ldrb r3, [r0, #1]",
        "lsr r3, r3, #4",
        "ldrb r12, [r0, #2]",
        "add r3, r3, r12, lsl #4",
        "mov r12, #3328",
        "sub r12, r12, r3",
        "add r2, r2, r12, lsr #31",
        "add r0, r0, #3",
        "subs r1, r1, #1",
        "bne 20b",
        "mov r3, #0",
        "sub r3, r3, r2",
        "lsr r3, r3, #31",
        "mov r0, #1",
        "sub r0, r0, r3",
        "bx lr",
    )
}
