// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mldsa` functions for `x86_64`.
#![allow(dead_code)]

/// `Power2Round` (FIPS 204 Algorithm 35) of each coefficient of `*t`: writes the `r1`s to `*t1` and the `r0`s, modulo `q` = 8380417, to `*t0`.
///
/// Contract: `VG.Spec.MlDsa.power2RoundContract`. Constant time: only the pointers may affect timing, not the data.
///
/// # Safety
///
/// * `t` must be valid for reads of 1024 bytes.
/// * `t1` must be valid for reads and writes of 1024 bytes.
/// * `t0` must be valid for reads and writes of 1024 bytes.
/// * Each of the 256 `u32`s of `t` must be less than `q` = 8380417.
/// * `t1` and `t0` must not overlap each other or `t` (distinct Rust objects never do).
/// * None of `t`, `t1` and `t0` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mldsa_power2round(t: *const [u32; 256], t1: *mut [u32; 256], t0: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov ecx, 256",
        "20:",
        "mov eax, DWORD PTR [rdi+rcx*4-4]",
        "add rax, 4095",
        "mov r8, rax",
        "shr r8, 13",
        "mov DWORD PTR [rsi+rcx*4-4], r8d",
        "and rax, 8191",
        "sub rax, 4095",
        "sbb r9, r9",
        "and r9, 8380417",
        "add rax, r9",
        "mov DWORD PTR [rdx+rcx*4-4], eax",
        "sub rcx, 1",
        "jne 20b",
        "ret",
    )
}

/// `HighBits` (FIPS 204 Algorithm 37) of each coefficient of `*r`, with `gamma2` = `γ₂`: writes the `r1`s to `*out`.
///
/// Contract: `VG.Spec.MlDsa.highBitsContract`. Constant time: only the pointers and `gamma2` may affect timing, not the data.
///
/// # Safety
///
/// * `r` must be valid for reads of 1024 bytes.
/// * `out` must be valid for reads and writes of 1024 bytes.
/// * `gamma2` must be (q - 1)/88 = 95232 or (q - 1)/32 = 261888.
/// * Each of the 256 `u32`s of `r` must be less than `q` = 8380417.
/// * `out` must not overlap `r` (distinct Rust objects never do).
/// * Neither `r` nor `out` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mldsa_high_bits(r: *const [u32; 256], gamma2: u32, out: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov esi, esi",
        "cmp esi, 261888",
        "mov r10, rdx",
        "je 20f",
        "mov ecx, 256",
        "22:",
        "mov eax, DWORD PTR [rdi+rcx*4-4]",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 11275",
        "mul r8",
        "add rax, 8388608",
        "shr rax, 24",
        "sub rax, 44",
        "sbb r8, r8",
        "and r8, 44",
        "add rax, r8",
        "mov DWORD PTR [r10+rcx*4-4], eax",
        "sub rcx, 1",
        "jne 22b",
        "jmp 21f",
        "20:",
        "mov ecx, 256",
        "23:",
        "mov eax, DWORD PTR [rdi+rcx*4-4]",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 1025",
        "mul r8",
        "add rax, 2097152",
        "shr rax, 22",
        "sub rax, 16",
        "sbb r8, r8",
        "and r8, 16",
        "add rax, r8",
        "mov DWORD PTR [r10+rcx*4-4], eax",
        "sub rcx, 1",
        "jne 23b",
        "21:",
        "ret",
    )
}

/// `LowBits` (FIPS 204 Algorithm 38) of each coefficient of `*r`, with `gamma2` = `γ₂`: writes the `r0`s, modulo `q` = 8380417, to `*out`.
///
/// Contract: `VG.Spec.MlDsa.lowBitsContract`. Constant time: only the pointers and `gamma2` may affect timing, not the data.
///
/// # Safety
///
/// * `r` must be valid for reads of 1024 bytes.
/// * `out` must be valid for reads and writes of 1024 bytes.
/// * `gamma2` must be (q - 1)/88 = 95232 or (q - 1)/32 = 261888.
/// * Each of the 256 `u32`s of `r` must be less than `q` = 8380417.
/// * `out` must not overlap `r` (distinct Rust objects never do).
/// * Neither `r` nor `out` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mldsa_low_bits(r: *const [u32; 256], gamma2: u32, out: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov esi, esi",
        "cmp esi, 261888",
        "mov r10, rdx",
        "je 20f",
        "mov ecx, 256",
        "22:",
        "mov eax, DWORD PTR [rdi+rcx*4-4]",
        "mov r11, rax",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 11275",
        "mul r8",
        "add rax, 8388608",
        "shr rax, 24",
        "sub rax, 44",
        "sbb r8, r8",
        "and r8, 44",
        "add rax, r8",
        "mov r8d, 190464",
        "mul r8",
        "sub r11, rax",
        "sbb r8, r8",
        "and r8, 8380417",
        "add r11, r8",
        "mov DWORD PTR [r10+rcx*4-4], r11d",
        "sub rcx, 1",
        "jne 22b",
        "jmp 21f",
        "20:",
        "mov ecx, 256",
        "23:",
        "mov eax, DWORD PTR [rdi+rcx*4-4]",
        "mov r11, rax",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 1025",
        "mul r8",
        "add rax, 2097152",
        "shr rax, 22",
        "sub rax, 16",
        "sbb r8, r8",
        "and r8, 16",
        "add rax, r8",
        "mov r8d, 523776",
        "mul r8",
        "sub r11, rax",
        "sbb r8, r8",
        "and r8, 8380417",
        "add r11, r8",
        "mov DWORD PTR [r10+rcx*4-4], r11d",
        "sub rcx, 1",
        "jne 23b",
        "21:",
        "ret",
    )
}

/// Returns 1 if the infinity norm of the polynomial `*f` (FIPS 204 §2.3: the largest `|fᵢ mod± q|`) is less than `bound`, and 0 otherwise.
///
/// Contract: `VG.Spec.MlDsa.normLtContract`. Constant time: only the pointer and `bound` may affect timing, not the data.
///
/// # Safety
///
/// * `f` must be valid for reads of 1024 bytes.
/// * Each of the 256 `u32`s of `f` must be less than `q` = 8380417.
/// * `f` must not overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mldsa_norm_lt(f: *const [u32; 256], bound: u32) -> u32 {
    core::arch::naked_asm!(
        "mov esi, esi",
        "mov r9, -1",
        "mov ecx, 256",
        "20:",
        "mov eax, DWORD PTR [rdi+rcx*4-4]",
        "mov edx, 8380417",
        "sub rdx, rax",
        "sub rax, rsi",
        "sub rdx, rsi",
        "or rax, rdx",
        "and r9, rax",
        "sub rcx, 1",
        "jne 20b",
        "mov rax, r9",
        "shr rax, 63",
        "ret",
    )
}

/// `MakeHint` (FIPS 204 Algorithm 39) of each pair of coefficients of `*z` and `*r`, with `gamma2` = `γ₂`: writes 1 for true and 0 for false to `*h`, and returns the number of 1s.
///
/// Contract: `VG.Spec.MlDsa.makeHintContract`. Constant time: only the pointers and `gamma2` may affect timing, not the data.
///
/// # Safety
///
/// * `z` must be valid for reads of 1024 bytes.
/// * `r` must be valid for reads of 1024 bytes.
/// * `h` must be valid for reads and writes of 1024 bytes.
/// * `gamma2` must be (q - 1)/88 = 95232 or (q - 1)/32 = 261888.
/// * Each of the 256 `u32`s of `z` must be less than `q` = 8380417.
/// * Each of the 256 `u32`s of `r` must be less than `q` = 8380417.
/// * `h` must not overlap `z` or `r` (distinct Rust objects never do).
/// * None of `z`, `r` and `h` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mldsa_make_hint(z: *const [u32; 256], r: *const [u32; 256], gamma2: u32, h: *mut [u32; 256]) -> u32 {
    core::arch::naked_asm!(
        "mov edx, edx",
        "cmp edx, 261888",
        "mov r10, rcx",
        "mov r9d, 0",
        "je 20f",
        "mov ecx, 256",
        "22:",
        "mov eax, DWORD PTR [rsi+rcx*4-4]",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 11275",
        "mul r8",
        "add rax, 8388608",
        "shr rax, 24",
        "sub rax, 44",
        "sbb r8, r8",
        "and r8, 44",
        "add rax, r8",
        "mov r11, rax",
        "mov eax, DWORD PTR [rsi+rcx*4-4]",
        "add eax, DWORD PTR [rdi+rcx*4-4]",
        "sub rax, 8380417",
        "sbb r8, r8",
        "and r8, 8380417",
        "add rax, r8",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 11275",
        "mul r8",
        "add rax, 8388608",
        "shr rax, 24",
        "sub rax, 44",
        "sbb r8, r8",
        "and r8, 44",
        "add rax, r8",
        "xor rax, r11",
        "add rax, 63",
        "shr rax, 6",
        "mov DWORD PTR [r10+rcx*4-4], eax",
        "add r9, rax",
        "sub rcx, 1",
        "jne 22b",
        "jmp 21f",
        "20:",
        "mov ecx, 256",
        "23:",
        "mov eax, DWORD PTR [rsi+rcx*4-4]",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 1025",
        "mul r8",
        "add rax, 2097152",
        "shr rax, 22",
        "sub rax, 16",
        "sbb r8, r8",
        "and r8, 16",
        "add rax, r8",
        "mov r11, rax",
        "mov eax, DWORD PTR [rsi+rcx*4-4]",
        "add eax, DWORD PTR [rdi+rcx*4-4]",
        "sub rax, 8380417",
        "sbb r8, r8",
        "and r8, 8380417",
        "add rax, r8",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 1025",
        "mul r8",
        "add rax, 2097152",
        "shr rax, 22",
        "sub rax, 16",
        "sbb r8, r8",
        "and r8, 16",
        "add rax, r8",
        "xor rax, r11",
        "add rax, 63",
        "shr rax, 6",
        "mov DWORD PTR [r10+rcx*4-4], eax",
        "add r9, rax",
        "sub rcx, 1",
        "jne 23b",
        "21:",
        "mov rax, r9",
        "ret",
    )
}

/// `UseHint` (FIPS 204 Algorithm 40) of each pair of coefficients of `*h` (a hint bit: true if it is not 0) and `*r`, with `gamma2` = `γ₂`: writes the results to `*out`.
///
/// Contract: `VG.Spec.MlDsa.useHintContract`. Constant time: only the pointers and `gamma2` may affect timing, not the data.
///
/// # Safety
///
/// * `h` must be valid for reads of 1024 bytes.
/// * `r` must be valid for reads of 1024 bytes.
/// * `out` must be valid for reads and writes of 1024 bytes.
/// * `gamma2` must be (q - 1)/88 = 95232 or (q - 1)/32 = 261888.
/// * Each of the 256 `u32`s of `r` must be less than `q` = 8380417.
/// * `out` must not overlap `h` or `r` (distinct Rust objects never do).
/// * None of `h`, `r` and `out` may overlap the return address on the stack, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_mldsa_use_hint(h: *const [u32; 256], r: *const [u32; 256], gamma2: u32, out: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "mov edx, edx",
        "cmp edx, 261888",
        "mov r10, rcx",
        "je 20f",
        "mov ecx, 256",
        "22:",
        "mov eax, DWORD PTR [rsi+rcx*4-4]",
        "mov r11, rax",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 11275",
        "mul r8",
        "add rax, 8388608",
        "shr rax, 24",
        "mov r9, rax",
        "mov r8d, 190464",
        "mul r8",
        "sub rax, r11",
        "sbb rax, rax",
        "and rax, 2",
        "sub rax, 1",
        "mov r11d, DWORD PTR [rdi+rcx*4-4]",
        "mov r8d, 0",
        "sub r8, r11",
        "sbb r8, r8",
        "and rax, r8",
        "add rax, r9",
        "add rax, 44",
        "sub rax, 44",
        "sbb r8, r8",
        "and r8, 44",
        "add rax, r8",
        "sub rax, 44",
        "sbb r8, r8",
        "and r8, 44",
        "add rax, r8",
        "mov DWORD PTR [r10+rcx*4-4], eax",
        "sub rcx, 1",
        "jne 22b",
        "jmp 21f",
        "20:",
        "mov ecx, 256",
        "23:",
        "mov eax, DWORD PTR [rsi+rcx*4-4]",
        "mov r11, rax",
        "add rax, 127",
        "shr rax, 7",
        "mov r8d, 1025",
        "mul r8",
        "add rax, 2097152",
        "shr rax, 22",
        "mov r9, rax",
        "mov r8d, 523776",
        "mul r8",
        "sub rax, r11",
        "sbb rax, rax",
        "and rax, 2",
        "sub rax, 1",
        "mov r11d, DWORD PTR [rdi+rcx*4-4]",
        "mov r8d, 0",
        "sub r8, r11",
        "sbb r8, r8",
        "and rax, r8",
        "add rax, r9",
        "add rax, 16",
        "sub rax, 16",
        "sbb r8, r8",
        "and r8, 16",
        "add rax, r8",
        "sub rax, 16",
        "sbb r8, r8",
        "and r8, 16",
        "add rax, r8",
        "mov DWORD PTR [r10+rcx*4-4], eax",
        "sub rcx, 1",
        "jne 23b",
        "21:",
        "ret",
    )
}
