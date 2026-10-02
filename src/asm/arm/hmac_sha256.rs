// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `hmac_sha256` functions for `arm`.
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
/// * `inner`, `outer` and `scratch` must not overlap each other, `key` or the arguments on the stack (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the 16 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "ldr r12, [sp, #0]",
        "str r4, [r12, #160]",
        "str r5, [r12, #164]",
        "str r6, [r12, #168]",
        "str r7, [r12, #172]",
        "str r8, [r12, #176]",
        "str r9, [r12, #180]",
        "str r10, [r12, #184]",
        "str lr, [r12, #188]",
        "str r11, [r12, #192]",
        "mov r4, r0",
        "mov r5, r1",
        "mov r6, r2",
        "mov r11, r12",
        "mov r8, #0",
        "mov r9, r3",
        "cmp r9, #0",
        "beq 20f",
        "22:",
        "add r2, r6, r8",
        "ldrb r12, [r2, #0]",
        "eor r1, r12, #54",
        "add r2, r11, r8",
        "strb r1, [r2, #196]",
        "eor r1, r12, #92",
        "strb r1, [r2, #260]",
        "add r8, r8, #1",
        "subs r9, r9, #1",
        "bne 22b",
        "b 21f",
        "20:",
        "21:",
        "movw r9, #64",
        "subs r9, r9, r8",
        "beq 23f",
        "25:",
        "add r2, r11, r8",
        "mov r1, #54",
        "strb r1, [r2, #196]",
        "mov r1, #92",
        "strb r1, [r2, #260]",
        "add r8, r8, #1",
        "subs r9, r9, #1",
        "bne 25b",
        "b 24f",
        "23:",
        "24:",
        "mov r0, r4",
        "bl {vg_sha256_init}",
        "mov r0, r4",
        "movw r12, #196",
        "add r1, r11, r12",
        "movw r7, #64",
        "mov r10, r11",
        "movw r2, #0",
        "mov r3, #0",
        "push {{r1, r7, r10, r12}}",
        "bl {vg_sha256_update}",
        "ldr r1, [sp], #16",
        "mov r0, r5",
        "bl {vg_sha256_init}",
        "mov r0, r5",
        "movw r12, #260",
        "add r1, r11, r12",
        "movw r7, #64",
        "mov r10, r11",
        "movw r2, #0",
        "mov r3, #0",
        "push {{r1, r7, r10, r12}}",
        "bl {vg_sha256_update}",
        "ldr r1, [sp], #16",
        "ldr r4, [r11, #160]",
        "ldr r5, [r11, #164]",
        "ldr r6, [r11, #168]",
        "ldr r7, [r11, #172]",
        "ldr r8, [r11, #176]",
        "ldr r9, [r11, #180]",
        "ldr r10, [r11, #184]",
        "ldr lr, [r11, #188]",
        "ldr r11, [r11, #192]",
        "bx lr",
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
/// * `inner`, `out` and `scratch` must not overlap each other, `outer` or the arguments on the stack (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the 16 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "ldr r12, [sp, #4]",
        "str r4, [r12, #160]",
        "str r5, [r12, #164]",
        "str r6, [r12, #168]",
        "str r7, [r12, #172]",
        "str r8, [r12, #176]",
        "str r9, [r12, #180]",
        "str r10, [r12, #184]",
        "str lr, [r12, #188]",
        "str r11, [r12, #192]",
        "mov r4, r0",
        "mov r5, r1",
        "ldr r6, [sp, #0]",
        "mov r11, r12",
        "mov r0, r4",
        "movw r12, #196",
        "add r1, r11, r12",
        "mov r12, r11",
        "push {{r1, r12}}",
        "bl {vg_sha256_finalize}",
        "ldr r1, [sp], #8",
        "mov r8, #0",
        "movw r9, #96",
        "20:",
        "add r2, r5, r8",
        "ldrb r12, [r2, #0]",
        "add r2, r4, r8",
        "strb r12, [r2, #0]",
        "add r8, r8, #1",
        "subs r9, r9, #1",
        "bne 20b",
        "mov r0, r4",
        "movw r12, #196",
        "add r1, r11, r12",
        "movw r7, #32",
        "mov r10, r11",
        "movw r2, #64",
        "mov r3, #0",
        "push {{r1, r7, r10, r12}}",
        "bl {vg_sha256_update}",
        "ldr r1, [sp], #16",
        "mov r0, r4",
        "movw r2, #96",
        "mov r3, #0",
        "movw r12, #196",
        "add r1, r11, r12",
        "mov r12, r11",
        "push {{r1, r12}}",
        "bl {vg_sha256_finalize}",
        "ldr r1, [sp], #8",
        "mov r8, #0",
        "movw r9, #32",
        "21:",
        "add r2, r11, r8",
        "ldrb r12, [r2, #196]",
        "add r2, r6, r8",
        "strb r12, [r2, #0]",
        "add r8, r8, #1",
        "subs r9, r9, #1",
        "bne 21b",
        "ldr r4, [r11, #160]",
        "ldr r5, [r11, #164]",
        "ldr r6, [r11, #168]",
        "ldr r7, [r11, #172]",
        "ldr r8, [r11, #176]",
        "ldr r9, [r11, #180]",
        "ldr r10, [r11, #184]",
        "ldr lr, [r11, #188]",
        "ldr r11, [r11, #192]",
        "bx lr",
        vg_sha256_finalize = sym super::sha256::vg_sha256_finalize,
        vg_sha256_update = sym super::sha256::vg_sha256_update,
    )
}
