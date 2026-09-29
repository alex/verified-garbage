// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem` functions for `x86_64`.
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
/// * Neither `f` nor `g` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_add(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "mov ecx, 256",
        "20:",
        "mov eax, DWORD PTR [rdi]",
        "add eax, DWORD PTR [rsi]",
        "sub eax, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add eax, edx",
        "mov DWORD PTR [rdi], eax",
        "add rdi, 4",
        "add rsi, 4",
        "sub rcx, 1",
        "jne 20b",
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
/// * Neither `f` nor `g` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_sub(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "mov ecx, 256",
        "20:",
        "mov eax, DWORD PTR [rdi]",
        "add eax, 3329",
        "sub eax, DWORD PTR [rsi]",
        "sub eax, 3329",
        "sbb edx, edx",
        "and edx, 3329",
        "add eax, edx",
        "mov DWORD PTR [rdi], eax",
        "add rdi, 4",
        "add rsi, 4",
        "sub rcx, 1",
        "jne 20b",
        "ret",
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
/// * Neither `f` nor `out` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_encode12(f: *const [u32; 256], out: *mut [u8; 384]) {
    core::arch::naked_asm!(
        "mov ecx, 128",
        "20:",
        "mov eax, DWORD PTR [rdi]",
        "mov edx, DWORD PTR [rdi+4]",
        "ror edx, 20",
        "add eax, edx",
        "mov BYTE PTR [rsi], al",
        "shr eax, 8",
        "mov BYTE PTR [rsi+1], al",
        "shr eax, 8",
        "mov BYTE PTR [rsi+2], al",
        "add rdi, 8",
        "add rsi, 3",
        "sub rcx, 1",
        "jne 20b",
        "ret",
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
/// * Neither `b` nor `f` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_decode12(b: *const [u8; 384], f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov ecx, 128",
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
        "sub eax, 3329",
        "sbb r8d, r8d",
        "and r8d, 3329",
        "add eax, r8d",
        "sub edx, 3329",
        "sbb r8d, r8d",
        "and r8d, 3329",
        "add edx, r8d",
        "mov DWORD PTR [rsi], eax",
        "mov DWORD PTR [rsi+4], edx",
        "add rdi, 3",
        "add rsi, 8",
        "sub rcx, 1",
        "jne 20b",
        "ret",
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
/// * Neither `b` nor `f` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_cbd2(b: *const [u8; 128], f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov ecx, 128",
        "20:",
        "movzx eax, BYTE PTR [rdi]",
        "mov edx, eax",
        "shr edx, 1",
        "and eax, 85",
        "and edx, 85",
        "add eax, edx",
        "mov edx, eax",
        "and edx, 3",
        "add edx, 3329",
        "mov r8d, eax",
        "shr r8d, 2",
        "and r8d, 3",
        "sub edx, r8d",
        "sub edx, 3329",
        "sbb r9d, r9d",
        "and r9d, 3329",
        "add edx, r9d",
        "mov DWORD PTR [rsi], edx",
        "mov edx, eax",
        "shr edx, 4",
        "and edx, 3",
        "add edx, 3329",
        "shr eax, 6",
        "sub edx, eax",
        "sub edx, 3329",
        "sbb r9d, r9d",
        "and r9d, 3329",
        "add edx, r9d",
        "mov DWORD PTR [rsi+4], edx",
        "add rdi, 1",
        "add rsi, 8",
        "sub rcx, 1",
        "jne 20b",
        "ret",
    )
}

/// `ByteEncode_d(Compress_d(f))` (FIPS 203 (4.7) and Algorithm 5): writes the 256 coefficients of `*f` (each less than `q` = 3329), compressed to `d` bits, to `out` as `d`-bit little-endian fields.
///
/// Contract: `VG.Spec.MlKem.compressEncodeContract`. Constant time: only the pointers, `d` and `len` may affect timing, not the data.
///
/// # Safety
///
/// * `d` must be 1, 4 or 10, and `len` must be `32 * d`.
/// * `f` must be valid for reads of 1024 bytes, and each of its 256 `u32`s must be less than 3329.
/// * `out` must be valid for writes of `len` bytes.
/// * `out` must not overlap `f` (distinct Rust objects never do).
/// * Neither `f` nor `out` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_compress_encode(f: *const [u32; 256], d: u32, out: *mut u8, len: usize) {
    core::arch::naked_asm!(
        "mov esi, esi",
        "mov r8, rdx",
        "cmp esi, 1",
        "je 20f",
        "cmp esi, 4",
        "je 22f",
        "mov r9, 161271",
        "mov ecx, 64",
        "24:",
        "mov r10d, 0",
        "mov eax, DWORD PTR [rdi+12]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1023",
        "ror r10, 54",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi+8]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1023",
        "ror r10, 54",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi+4]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1023",
        "ror r10, 54",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1023",
        "ror r10, 54",
        "add r10, rax",
        "mov BYTE PTR [r8], r10b",
        "shr r10, 8",
        "mov BYTE PTR [r8+1], r10b",
        "shr r10, 8",
        "mov BYTE PTR [r8+2], r10b",
        "shr r10, 8",
        "mov BYTE PTR [r8+3], r10b",
        "shr r10, 8",
        "mov BYTE PTR [r8+4], r10b",
        "shr r10, 8",
        "add rdi, 16",
        "add r8, 5",
        "sub rcx, 1",
        "jne 24b",
        "jmp 23f",
        "22:",
        "mov r9, 2520",
        "mov ecx, 128",
        "25:",
        "mov r10d, 0",
        "mov eax, DWORD PTR [rdi+4]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 15",
        "ror r10, 60",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 15",
        "ror r10, 60",
        "add r10, rax",
        "mov BYTE PTR [r8], r10b",
        "shr r10, 8",
        "add rdi, 8",
        "add r8, 1",
        "sub rcx, 1",
        "jne 25b",
        "23:",
        "jmp 21f",
        "20:",
        "mov r9, 315",
        "mov ecx, 32",
        "26:",
        "mov r10d, 0",
        "mov eax, DWORD PTR [rdi+28]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1",
        "ror r10, 63",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi+24]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1",
        "ror r10, 63",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi+20]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1",
        "ror r10, 63",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi+16]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1",
        "ror r10, 63",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi+12]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1",
        "ror r10, 63",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi+8]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1",
        "ror r10, 63",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi+4]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1",
        "ror r10, 63",
        "add r10, rax",
        "mov eax, DWORD PTR [rdi]",
        "mul r9",
        "add rax, 262080",
        "shr rax, 19",
        "and eax, 1",
        "ror r10, 63",
        "add r10, rax",
        "mov BYTE PTR [r8], r10b",
        "shr r10, 8",
        "add rdi, 32",
        "add r8, 1",
        "sub rcx, 1",
        "jne 26b",
        "21:",
        "ret",
    )
}

/// `Decompress_d(ByteDecode_d(b))` (FIPS 203 Algorithm 6 and (4.8)): writes the 256 `d`-bit little-endian fields of the `len` bytes at `b`, decompressed, to `*f` (each less than `q` = 3329).
///
/// Contract: `VG.Spec.MlKem.decodeDecompressContract`. Constant time: only the pointers, `d` and `len` may affect timing, not the data.
///
/// # Safety
///
/// * `d` must be 1, 4 or 10, and `len` must be `32 * d`.
/// * `b` must be valid for reads of `len` bytes.
/// * `f` must be valid for writes of 1024 bytes.
/// * `f` must not overlap `b` (distinct Rust objects never do).
/// * Neither `b` nor `f` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mlkem_decode_decompress(b: *const u8, len: usize, d: u32, f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov edx, edx",
        "mov rsi, rcx",
        "cmp edx, 1",
        "je 20f",
        "cmp edx, 4",
        "je 22f",
        "mov r9, 3329",
        "mov ecx, 64",
        "24:",
        "mov r10d, 0",
        "movzx eax, BYTE PTR [rdi+4]",
        "ror r10, 56",
        "add r10, rax",
        "movzx eax, BYTE PTR [rdi+3]",
        "ror r10, 56",
        "add r10, rax",
        "movzx eax, BYTE PTR [rdi+2]",
        "ror r10, 56",
        "add r10, rax",
        "movzx eax, BYTE PTR [rdi+1]",
        "ror r10, 56",
        "add r10, rax",
        "movzx eax, BYTE PTR [rdi]",
        "ror r10, 56",
        "add r10, rax",
        "mov rax, r10",
        "and eax, 1023",
        "mul r9",
        "add rax, 512",
        "shr rax, 10",
        "mov DWORD PTR [rsi], eax",
        "shr r10, 10",
        "mov rax, r10",
        "and eax, 1023",
        "mul r9",
        "add rax, 512",
        "shr rax, 10",
        "mov DWORD PTR [rsi+4], eax",
        "shr r10, 10",
        "mov rax, r10",
        "and eax, 1023",
        "mul r9",
        "add rax, 512",
        "shr rax, 10",
        "mov DWORD PTR [rsi+8], eax",
        "shr r10, 10",
        "mov rax, r10",
        "and eax, 1023",
        "mul r9",
        "add rax, 512",
        "shr rax, 10",
        "mov DWORD PTR [rsi+12], eax",
        "shr r10, 10",
        "add rdi, 5",
        "add rsi, 16",
        "sub rcx, 1",
        "jne 24b",
        "jmp 23f",
        "22:",
        "mov r9, 3329",
        "mov ecx, 128",
        "25:",
        "mov r10d, 0",
        "movzx eax, BYTE PTR [rdi]",
        "ror r10, 56",
        "add r10, rax",
        "mov rax, r10",
        "and eax, 15",
        "mul r9",
        "add rax, 8",
        "shr rax, 4",
        "mov DWORD PTR [rsi], eax",
        "shr r10, 4",
        "mov rax, r10",
        "and eax, 15",
        "mul r9",
        "add rax, 8",
        "shr rax, 4",
        "mov DWORD PTR [rsi+4], eax",
        "shr r10, 4",
        "add rdi, 1",
        "add rsi, 8",
        "sub rcx, 1",
        "jne 25b",
        "23:",
        "jmp 21f",
        "20:",
        "mov r9, 3329",
        "mov ecx, 32",
        "26:",
        "mov r10d, 0",
        "movzx eax, BYTE PTR [rdi]",
        "ror r10, 56",
        "add r10, rax",
        "mov rax, r10",
        "and eax, 1",
        "mul r9",
        "add rax, 1",
        "shr rax, 1",
        "mov DWORD PTR [rsi], eax",
        "shr r10, 1",
        "mov rax, r10",
        "and eax, 1",
        "mul r9",
        "add rax, 1",
        "shr rax, 1",
        "mov DWORD PTR [rsi+4], eax",
        "shr r10, 1",
        "mov rax, r10",
        "and eax, 1",
        "mul r9",
        "add rax, 1",
        "shr rax, 1",
        "mov DWORD PTR [rsi+8], eax",
        "shr r10, 1",
        "mov rax, r10",
        "and eax, 1",
        "mul r9",
        "add rax, 1",
        "shr rax, 1",
        "mov DWORD PTR [rsi+12], eax",
        "shr r10, 1",
        "mov rax, r10",
        "and eax, 1",
        "mul r9",
        "add rax, 1",
        "shr rax, 1",
        "mov DWORD PTR [rsi+16], eax",
        "shr r10, 1",
        "mov rax, r10",
        "and eax, 1",
        "mul r9",
        "add rax, 1",
        "shr rax, 1",
        "mov DWORD PTR [rsi+20], eax",
        "shr r10, 1",
        "mov rax, r10",
        "and eax, 1",
        "mul r9",
        "add rax, 1",
        "shr rax, 1",
        "mov DWORD PTR [rsi+24], eax",
        "shr r10, 1",
        "mov rax, r10",
        "and eax, 1",
        "mul r9",
        "add rax, 1",
        "shr rax, 1",
        "mov DWORD PTR [rsi+28], eax",
        "shr r10, 1",
        "add rdi, 1",
        "add rsi, 32",
        "sub rcx, 1",
        "jne 26b",
        "21:",
        "ret",
    )
}
