// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem768` functions for `x86_64`.
#![allow(dead_code)]

/// The ML-KEM-768 encapsulation key check (FIPS 203 §7.2): returns 1 if every 12-bit integer that the first 1152 bytes of `*ek` encode is less than `q` = 3329 (the modulus check), and 0 otherwise. An encapsulation key must pass it before it is given to `vg_mlkem768_encaps`.
///
/// Contract: `VG.Spec.MlKem.checkEkContract`. Constant time: only the pointer may affect timing.
///
/// # Safety
///
/// * `ek` must be valid for reads of 1184 bytes.
/// * `ek` must not overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem768_check_ek(ek: *const [u8; 1184]) -> u32 {
    core::arch::naked_asm!(
        "mov r8d, 0",
        "mov ecx, 384",
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
        "cmp eax, 3329",
        "adc r8, 0",
        "cmp edx, 3329",
        "adc r8, 0",
        "add rdi, 3",
        "sub rcx, 1",
        "jne 20b",
        "cmp r8, 768",
        "sbb rax, rax",
        "add rax, 1",
        "ret",
    )
}
