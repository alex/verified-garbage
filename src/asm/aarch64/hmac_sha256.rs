// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `hmac_sha256` functions for `aarch64`.
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
/// * `inner`, `outer` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `key` and `scratch` may overlap the 16 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "str x19, [x4, #160]",
        "str x20, [x4, #168]",
        "str x21, [x4, #176]",
        "str x22, [x4, #184]",
        "str x24, [x4, #192]",
        "str x30, [x4, #200]",
        "str x23, [x4, #208]",
        "add x19, x0, #0",
        "add x20, x1, #0",
        "add x21, x2, #0",
        "add x22, x3, #0",
        "add x23, x4, #0",
        "movz x14, #54, lsl #0",
        "movz x15, #92, lsl #0",
        "movz x24, #0, lsl #0",
        "cbz x22, 20f",
        "22:",
        "add x13, x21, x24",
        "ldrb w9, [x13, #0]",
        "add x12, x23, x24",
        "eor x10, x9, x14",
        "strb w10, [x12, #216]",
        "eor x10, x9, x15",
        "strb w10, [x12, #280]",
        "add x24, x24, #1",
        "sub x11, x22, x24",
        "cbnz x11, 22b",
        "b 21f",
        "20:",
        "21:",
        "movz x11, #64, lsl #0",
        "sub x11, x11, x24",
        "cbz x11, 23f",
        "25:",
        "add x12, x23, x24",
        "strb w14, [x12, #216]",
        "strb w15, [x12, #280]",
        "add x24, x24, #1",
        "movz x11, #64, lsl #0",
        "sub x11, x11, x24",
        "cbnz x11, 25b",
        "b 24f",
        "23:",
        "24:",
        "add x0, x19, #0",
        "bl {vg_sha256_init}",
        "add x0, x19, #0",
        "movz x1, #0, lsl #0",
        "add x2, x23, #216",
        "movz x3, #64, lsl #0",
        "add x4, x23, #0",
        "bl {vg_sha256_update}",
        "add x0, x20, #0",
        "bl {vg_sha256_init}",
        "add x0, x20, #0",
        "movz x1, #0, lsl #0",
        "add x2, x23, #280",
        "movz x3, #64, lsl #0",
        "add x4, x23, #0",
        "bl {vg_sha256_update}",
        "ldr x19, [x23, #160]",
        "ldr x20, [x23, #168]",
        "ldr x21, [x23, #176]",
        "ldr x22, [x23, #184]",
        "ldr x24, [x23, #192]",
        "ldr x30, [x23, #200]",
        "ldr x23, [x23, #208]",
        "ret",
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
/// * `inner`, `out` and `scratch` must not overlap each other or `outer` (distinct Rust objects never do).
/// * None of `inner`, `outer`, `out` and `scratch` may overlap the 16 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 104]) {
    core::arch::naked_asm!(
        "str x19, [x4, #160]",
        "str x20, [x4, #168]",
        "str x21, [x4, #176]",
        "str x22, [x4, #184]",
        "str x24, [x4, #192]",
        "str x30, [x4, #200]",
        "str x23, [x4, #208]",
        "add x19, x0, #0",
        "add x20, x1, #0",
        "add x21, x3, #0",
        "add x23, x4, #0",
        "add x1, x2, #0",
        "add x2, x23, #216",
        "add x3, x23, #0",
        "bl {vg_sha256_finalize}",
        "ldr w9, [x20, #0]",
        "str w9, [x19, #0]",
        "ldr w9, [x20, #4]",
        "str w9, [x19, #4]",
        "ldr w9, [x20, #8]",
        "str w9, [x19, #8]",
        "ldr w9, [x20, #12]",
        "str w9, [x19, #12]",
        "ldr w9, [x20, #16]",
        "str w9, [x19, #16]",
        "ldr w9, [x20, #20]",
        "str w9, [x19, #20]",
        "ldr w9, [x20, #24]",
        "str w9, [x19, #24]",
        "ldr w9, [x20, #28]",
        "str w9, [x19, #28]",
        "ldr w9, [x23, #216]",
        "str w9, [x19, #32]",
        "ldr w9, [x23, #220]",
        "str w9, [x19, #36]",
        "ldr w9, [x23, #224]",
        "str w9, [x19, #40]",
        "ldr w9, [x23, #228]",
        "str w9, [x19, #44]",
        "ldr w9, [x23, #232]",
        "str w9, [x19, #48]",
        "ldr w9, [x23, #236]",
        "str w9, [x19, #52]",
        "ldr w9, [x23, #240]",
        "str w9, [x19, #56]",
        "ldr w9, [x23, #244]",
        "str w9, [x19, #60]",
        "add x0, x19, #0",
        "movz x1, #96, lsl #0",
        "add x2, x23, #216",
        "add x3, x23, #0",
        "bl {vg_sha256_finalize}",
        "ldr w9, [x23, #216]",
        "str w9, [x21, #0]",
        "ldr w9, [x23, #220]",
        "str w9, [x21, #4]",
        "ldr w9, [x23, #224]",
        "str w9, [x21, #8]",
        "ldr w9, [x23, #228]",
        "str w9, [x21, #12]",
        "ldr w9, [x23, #232]",
        "str w9, [x21, #16]",
        "ldr w9, [x23, #236]",
        "str w9, [x21, #20]",
        "ldr w9, [x23, #240]",
        "str w9, [x21, #24]",
        "ldr w9, [x23, #244]",
        "str w9, [x21, #28]",
        "ldr x19, [x23, #160]",
        "ldr x20, [x23, #168]",
        "ldr x21, [x23, #176]",
        "ldr x22, [x23, #184]",
        "ldr x24, [x23, #192]",
        "ldr x30, [x23, #200]",
        "ldr x23, [x23, #208]",
        "ret",
        vg_sha256_finalize = sym super::sha256::vg_sha256_finalize,
    )
}
