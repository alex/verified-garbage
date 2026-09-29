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

/// `SamplePolyCBD₂` (FIPS 203 Algorithm 8 with `η` = 2): writes the polynomial sampled from the 128 bytes `*b` to `*f` (256 coefficients less than `q` = 3329).
///
/// Contract: `VG.Spec.MlKem.cbd2Contract`. Constant time: only the pointers may affect timing, not the data.
///
/// # Safety
///
/// * `b` must be valid for reads of 128 bytes.
/// * `f` must be valid for writes of 1024 bytes.
/// * `f` must not overlap `b` (distinct Rust objects never do).
/// * Neither `b` nor `f` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_cbd2(b: *const [u8; 128], f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov r2, #128",
        "20:",
        "ldrb r3, [r0, #0]",
        "lsl r3, r3, #30",
        "lsr r3, r3, #30",
        "sub r3, r3, r3, lsr #1",
        "ldrb r12, [r0, #0]",
        "lsl r12, r12, #28",
        "lsr r12, r12, #30",
        "sub r12, r12, r12, lsr #1",
        "sub r3, r3, r12",
        "lsr r12, r3, #31",
        "add r3, r3, r12",
        "add r3, r3, r12, lsl #8",
        "add r3, r3, r12, lsl #10",
        "add r3, r3, r12, lsl #11",
        "str r3, [r1, #0]",
        "ldrb r3, [r0, #0]",
        "lsl r3, r3, #26",
        "lsr r3, r3, #30",
        "sub r3, r3, r3, lsr #1",
        "ldrb r12, [r0, #0]",
        "lsl r12, r12, #24",
        "lsr r12, r12, #30",
        "sub r12, r12, r12, lsr #1",
        "sub r3, r3, r12",
        "lsr r12, r3, #31",
        "add r3, r3, r12",
        "add r3, r3, r12, lsl #8",
        "add r3, r3, r12, lsl #10",
        "add r3, r3, r12, lsl #11",
        "str r3, [r1, #4]",
        "add r0, r0, #1",
        "add r1, r1, #8",
        "subs r2, r2, #1",
        "bne 20b",
        "bx lr",
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
/// * Neither `f` nor `out` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_encode12(f: *const [u32; 256], out: *mut [u8; 384]) {
    core::arch::naked_asm!(
        "mov r2, #128",
        "20:",
        "ldr r3, [r0, #0]",
        "ldr r12, [r0, #4]",
        "strb r3, [r1, #0]",
        "lsr r3, r3, #8",
        "add r3, r3, r12, lsl #4",
        "strb r3, [r1, #1]",
        "lsr r12, r12, #4",
        "strb r12, [r1, #2]",
        "add r0, r0, #8",
        "add r1, r1, #3",
        "subs r2, r2, #1",
        "bne 20b",
        "bx lr",
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
/// * Neither `b` nor `f` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_decode12(b: *const [u8; 384], f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov r2, #128",
        "20:",
        "ldrb r3, [r0, #0]",
        "ldrb r12, [r0, #1]",
        "lsl r12, r12, #28",
        "add r3, r3, r12, lsr #20",
        "sub r3, r3, #3328",
        "sub r3, r3, #1",
        "lsr r12, r3, #31",
        "add r3, r3, r12",
        "add r3, r3, r12, lsl #8",
        "add r3, r3, r12, lsl #10",
        "add r3, r3, r12, lsl #11",
        "str r3, [r1, #0]",
        "ldrb r3, [r0, #1]",
        "lsr r3, r3, #4",
        "ldrb r12, [r0, #2]",
        "add r3, r3, r12, lsl #4",
        "sub r3, r3, #3328",
        "sub r3, r3, #1",
        "lsr r12, r3, #31",
        "add r3, r3, r12",
        "add r3, r3, r12, lsl #8",
        "add r3, r3, r12, lsl #10",
        "add r3, r3, r12, lsl #11",
        "str r3, [r1, #4]",
        "add r0, r0, #3",
        "add r1, r1, #8",
        "subs r2, r2, #1",
        "bne 20b",
        "bx lr",
    )
}
