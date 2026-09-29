// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem` functions for `x86`.
#![allow(dead_code)]

/// Adds the polynomial `*g` to `*f` modulo `q` = 3329, coefficient by coefficient (FIPS 203 (2.3)).
///
/// Contract: `VG.Spec.MlKem.addContract`. Constant time: only the pointers may affect timing, not the data.
///
/// The function may overwrite the arguments on the stack, as the calling convention lets it.
///
/// # Safety
///
/// * `f` must be valid for reads and writes of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `g` must be valid for reads of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `f` must not overlap `g` (distinct Rust objects never do).
/// * Neither `f` nor `g` may overlap the arguments on the stack, overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_add(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "push ebx",
        "push esi",
        "push edi",
        "push ebp",
        "mov esi, DWORD PTR [esp+20]",
        "mov edi, DWORD PTR [esp+24]",
        "mov ecx, 256",
        "20:",
        "mov eax, DWORD PTR [esi]",
        "add eax, DWORD PTR [edi]",
        "sub eax, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add eax, edx",
        "mov DWORD PTR [esi], eax",
        "add esi, 4",
        "add edi, 4",
        "sub ecx, 1",
        "jne 20b",
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

/// Subtracts the polynomial `*g` from `*f` modulo `q` = 3329, coefficient by coefficient.
///
/// Contract: `VG.Spec.MlKem.subContract`. Constant time: only the pointers may affect timing, not the data.
///
/// The function may overwrite the arguments on the stack, as the calling convention lets it.
///
/// # Safety
///
/// * `f` must be valid for reads and writes of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `g` must be valid for reads of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `f` must not overlap `g` (distinct Rust objects never do).
/// * Neither `f` nor `g` may overlap the arguments on the stack, overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_sub(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "push ebx",
        "push esi",
        "push edi",
        "push ebp",
        "mov esi, DWORD PTR [esp+20]",
        "mov edi, DWORD PTR [esp+24]",
        "mov ecx, 256",
        "20:",
        "mov eax, DWORD PTR [esi]",
        "add eax, 3329",
        "sub eax, DWORD PTR [edi]",
        "sub eax, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add eax, edx",
        "mov DWORD PTR [esi], eax",
        "add esi, 4",
        "add edi, 4",
        "sub ecx, 1",
        "jne 20b",
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

/// `ByteEncode₁₂` (FIPS 203 Algorithm 5): writes the 256 coefficients of `*f`, each less than `q` = 3329, to `*out` as 12-bit little-endian fields.
///
/// Contract: `VG.Spec.MlKem.encode12Contract`. Constant time: only the pointers may affect timing, not the data.
///
/// The function may overwrite the arguments on the stack, as the calling convention lets it.
///
/// # Safety
///
/// * `f` must be valid for reads of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `out` must be valid for writes of 384 bytes.
/// * `out` must not overlap `f` (distinct Rust objects never do).
/// * Neither `f` nor `out` may overlap the arguments on the stack, overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_encode12(f: *const [u32; 256], out: *mut [u8; 384]) {
    core::arch::naked_asm!(
        "push ebx",
        "push esi",
        "push edi",
        "push ebp",
        "mov esi, DWORD PTR [esp+20]",
        "mov edi, DWORD PTR [esp+24]",
        "mov ecx, 128",
        "20:",
        "mov eax, DWORD PTR [esi]",
        "mov edx, DWORD PTR [esi+4]",
        "ror edx, 20",
        "add eax, edx",
        "mov BYTE PTR [edi], al",
        "shr eax, 8",
        "mov BYTE PTR [edi+1], al",
        "shr eax, 8",
        "mov BYTE PTR [edi+2], al",
        "add esi, 8",
        "add edi, 3",
        "sub ecx, 1",
        "jne 20b",
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

/// `ByteDecode₁₂` (FIPS 203 Algorithm 6): writes the 256 12-bit little-endian fields of `*b`, each reduced modulo `q` = 3329, to `*f`.
///
/// Contract: `VG.Spec.MlKem.decode12Contract`. Constant time: only the pointers may affect timing, not the data.
///
/// The function may overwrite the arguments on the stack, as the calling convention lets it.
///
/// # Safety
///
/// * `b` must be valid for reads of 384 bytes.
/// * `f` must be valid for writes of 1024 bytes.
/// * `f` must not overlap `b` (distinct Rust objects never do).
/// * Neither `b` nor `f` may overlap the arguments on the stack, overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_decode12(b: *const [u8; 384], f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "push ebx",
        "push esi",
        "push edi",
        "push ebp",
        "mov esi, DWORD PTR [esp+20]",
        "mov edi, DWORD PTR [esp+24]",
        "mov ecx, 128",
        "20:",
        "movzx eax, BYTE PTR [esi]",
        "movzx ebx, BYTE PTR [esi+1]",
        "movzx edx, BYTE PTR [esi+2]",
        "mov ebp, ebx",
        "shr ebp, 4",
        "ror edx, 28",
        "add ebp, edx",
        "and ebx, 15",
        "ror ebx, 24",
        "add eax, ebx",
        "sub eax, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add eax, edx",
        "mov DWORD PTR [edi], eax",
        "sub ebp, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add ebp, edx",
        "mov DWORD PTR [edi+4], ebp",
        "add esi, 3",
        "add edi, 8",
        "sub ecx, 1",
        "jne 20b",
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

/// `SamplePolyCBD₂` (FIPS 203 Algorithm 8 with `η` = 2): writes the polynomial sampled from the 128 bytes `*b` to `*f` (256 coefficients less than `q` = 3329).
///
/// Contract: `VG.Spec.MlKem.cbd2Contract`. Constant time: only the pointers may affect timing, not the data.
///
/// The function may overwrite the arguments on the stack, as the calling convention lets it.
///
/// # Safety
///
/// * `b` must be valid for reads of 128 bytes.
/// * `f` must be valid for writes of 1024 bytes.
/// * `f` must not overlap `b` (distinct Rust objects never do).
/// * Neither `b` nor `f` may overlap the arguments on the stack, overlap the return address on the stack or the 16 bytes of stack below it, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_cbd2(b: *const [u8; 128], f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "push ebx",
        "push esi",
        "push edi",
        "push ebp",
        "mov esi, DWORD PTR [esp+20]",
        "mov edi, DWORD PTR [esp+24]",
        "mov ecx, 128",
        "20:",
        "movzx ebx, BYTE PTR [esi]",
        "mov eax, ebx",
        "mov edx, eax",
        "shr edx, 1",
        "and eax, 5",
        "and edx, 5",
        "add eax, edx",
        "mov edx, eax",
        "shr edx, 2",
        "and eax, 3",
        "add eax, 3329",
        "sub eax, edx",
        "sub eax, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add eax, edx",
        "mov DWORD PTR [edi], eax",
        "mov eax, ebx",
        "shr eax, 4",
        "mov edx, eax",
        "shr edx, 1",
        "and eax, 5",
        "and edx, 5",
        "add eax, edx",
        "mov edx, eax",
        "shr edx, 2",
        "and eax, 3",
        "add eax, 3329",
        "sub eax, edx",
        "sub eax, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add eax, edx",
        "mov DWORD PTR [edi+4], eax",
        "add esi, 1",
        "add edi, 8",
        "sub ecx, 1",
        "jne 20b",
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
