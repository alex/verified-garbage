// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem768` functions for `x86`.
#![allow(dead_code)]

/// The ML-KEM-768 encapsulation key check (FIPS 203 §7.2): returns 1 if every 12-bit integer that the first 1152 bytes of `*ek` encode is less than `q` = 3329 (the modulus check), and 0 otherwise. An encapsulation key must pass it before it is given to `vg_mlkem768_encaps`.
///
/// Contract: `VG.Spec.MlKem.checkEkContract`. Constant time: only the pointer may affect timing.
///
/// # Safety
///
/// * `ek` must be valid for reads of 1184 bytes.
/// * `ek` must not overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem768_check_ek(ek: *const [u8; 1184]) -> u32 {
    core::arch::naked_asm!(
        "push ebx",
        "push esi",
        "push edi",
        "push ebp",
        "mov esi, DWORD PTR [esp+20]",
        "mov ecx, 384",
        "mov ebx, -1",
        "20:",
        "movzx eax, BYTE PTR [esi]",
        "movzx edx, BYTE PTR [esi+1]",
        "mov ebp, edx",
        "and edx, 15",
        "ror edx, 24",
        "add eax, edx",
        "shr ebp, 4",
        "movzx edx, BYTE PTR [esi+2]",
        "ror edx, 28",
        "add ebp, edx",
        "sub eax, 3329",
        "sbb eax, eax",
        "and ebx, eax",
        "sub ebp, 3329",
        "sbb ebp, ebp",
        "and ebx, ebp",
        "add esi, 3",
        "sub ecx, 1",
        "jne 20b",
        "mov eax, ebx",
        "and eax, 1",
        "mov esi, DWORD PTR [esp+8]",
        "mov edi, DWORD PTR [esp+4]",
        "mov ebp, DWORD PTR [esp]",
        "pop ebx",
        "pop ebx",
        "pop ebx",
        "pop ebx",
        "ret",
    )
}
