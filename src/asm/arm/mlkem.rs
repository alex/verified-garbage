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
/// * Neither `f` nor `out` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_compress_encode(f: *const [u32; 256], d: u32, out: *mut u8, len: usize) {
    core::arch::naked_asm!(
        "cmp r1, #1",
        "beq 20f",
        "cmp r1, #4",
        "beq 22f",
        "mov r3, #64",
        "24:",
        "ldr r1, [r0, #0]",
        "movw r12, #30199",
        "movt r12, #2",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #22",
        "lsr r1, r1, #22",
        "strb r1, [r2, #0]",
        "lsr r1, r1, #8",
        "strb r1, [r2, #1]",
        "ldr r1, [r0, #4]",
        "movw r12, #30199",
        "movt r12, #2",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #22",
        "lsr r1, r1, #22",
        "ldrb r12, [r2, #1]",
        "add r12, r12, r1, lsl #2",
        "strb r12, [r2, #1]",
        "lsr r1, r1, #6",
        "strb r1, [r2, #2]",
        "ldr r1, [r0, #8]",
        "movw r12, #30199",
        "movt r12, #2",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #22",
        "lsr r1, r1, #22",
        "ldrb r12, [r2, #2]",
        "add r12, r12, r1, lsl #4",
        "strb r12, [r2, #2]",
        "lsr r1, r1, #4",
        "strb r1, [r2, #3]",
        "ldr r1, [r0, #12]",
        "movw r12, #30199",
        "movt r12, #2",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #22",
        "lsr r1, r1, #22",
        "ldrb r12, [r2, #3]",
        "add r12, r12, r1, lsl #6",
        "strb r12, [r2, #3]",
        "lsr r1, r1, #2",
        "strb r1, [r2, #4]",
        "add r0, r0, #16",
        "add r2, r2, #5",
        "subs r3, r3, #1",
        "bne 24b",
        "b 23f",
        "22:",
        "mov r3, #128",
        "25:",
        "ldr r1, [r0, #0]",
        "movw r12, #2520",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #28",
        "lsr r1, r1, #28",
        "strb r1, [r2, #0]",
        "ldr r1, [r0, #4]",
        "movw r12, #2520",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #28",
        "ldrb r12, [r2, #0]",
        "add r12, r12, r1, lsr #24",
        "strb r12, [r2, #0]",
        "add r0, r0, #8",
        "add r2, r2, #1",
        "subs r3, r3, #1",
        "bne 25b",
        "23:",
        "b 21f",
        "20:",
        "mov r3, #32",
        "26:",
        "mov r12, #0",
        "strb r12, [r2, #0]",
        "ldr r1, [r0, #0]",
        "movw r12, #315",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #31",
        "ldrb r12, [r2, #0]",
        "add r12, r12, r1, lsr #31",
        "strb r12, [r2, #0]",
        "ldr r1, [r0, #4]",
        "movw r12, #315",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #31",
        "ldrb r12, [r2, #0]",
        "add r12, r12, r1, lsr #30",
        "strb r12, [r2, #0]",
        "ldr r1, [r0, #8]",
        "movw r12, #315",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #31",
        "ldrb r12, [r2, #0]",
        "add r12, r12, r1, lsr #29",
        "strb r12, [r2, #0]",
        "ldr r1, [r0, #12]",
        "movw r12, #315",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #31",
        "ldrb r12, [r2, #0]",
        "add r12, r12, r1, lsr #28",
        "strb r12, [r2, #0]",
        "ldr r1, [r0, #16]",
        "movw r12, #315",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #31",
        "ldrb r12, [r2, #0]",
        "add r12, r12, r1, lsr #27",
        "strb r12, [r2, #0]",
        "ldr r1, [r0, #20]",
        "movw r12, #315",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #31",
        "ldrb r12, [r2, #0]",
        "add r12, r12, r1, lsr #26",
        "strb r12, [r2, #0]",
        "ldr r1, [r0, #24]",
        "movw r12, #315",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #31",
        "ldrb r12, [r2, #0]",
        "add r12, r12, r1, lsr #25",
        "strb r12, [r2, #0]",
        "ldr r1, [r0, #28]",
        "movw r12, #315",
        "mul r1, r1, r12",
        "add r1, r1, #262144",
        "sub r1, r1, #64",
        "lsr r1, r1, #19",
        "lsl r1, r1, #31",
        "ldrb r12, [r2, #0]",
        "add r12, r12, r1, lsr #24",
        "strb r12, [r2, #0]",
        "add r0, r0, #32",
        "add r2, r2, #1",
        "subs r3, r3, #1",
        "bne 26b",
        "21:",
        "bx lr",
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
/// * Neither `b` nor `f` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_decode_decompress(b: *const u8, len: usize, d: u32, f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "cmp r2, #1",
        "beq 20f",
        "cmp r2, #4",
        "beq 22f",
        "24:",
        "ldrb r2, [r0, #1]",
        "lsl r2, r2, #30",
        "lsr r2, r2, #22",
        "ldrb r12, [r0, #0]",
        "add r2, r2, r12",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #512",
        "lsr r12, r12, #10",
        "str r12, [r3, #0]",
        "ldrb r2, [r0, #2]",
        "lsl r2, r2, #28",
        "lsr r2, r2, #22",
        "ldrb r12, [r0, #1]",
        "add r2, r2, r12, lsr #2",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #512",
        "lsr r12, r12, #10",
        "str r12, [r3, #4]",
        "ldrb r2, [r0, #3]",
        "lsl r2, r2, #26",
        "lsr r2, r2, #22",
        "ldrb r12, [r0, #2]",
        "add r2, r2, r12, lsr #4",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #512",
        "lsr r12, r12, #10",
        "str r12, [r3, #8]",
        "ldrb r2, [r0, #4]",
        "lsl r2, r2, #2",
        "ldrb r12, [r0, #3]",
        "add r2, r2, r12, lsr #6",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #512",
        "lsr r12, r12, #10",
        "str r12, [r3, #12]",
        "add r0, r0, #5",
        "add r3, r3, #16",
        "subs r1, r1, #5",
        "bne 24b",
        "b 23f",
        "22:",
        "25:",
        "ldrb r2, [r0, #0]",
        "lsl r2, r2, #28",
        "lsr r2, r2, #28",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #8",
        "lsr r12, r12, #4",
        "str r12, [r3, #0]",
        "ldrb r2, [r0, #0]",
        "lsr r2, r2, #4",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #8",
        "lsr r12, r12, #4",
        "str r12, [r3, #4]",
        "add r0, r0, #1",
        "add r3, r3, #8",
        "subs r1, r1, #1",
        "bne 25b",
        "23:",
        "b 21f",
        "20:",
        "26:",
        "ldrb r2, [r0, #0]",
        "lsl r2, r2, #31",
        "lsr r2, r2, #31",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #1",
        "lsr r12, r12, #1",
        "str r12, [r3, #0]",
        "ldrb r2, [r0, #0]",
        "lsl r2, r2, #30",
        "lsr r2, r2, #31",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #1",
        "lsr r12, r12, #1",
        "str r12, [r3, #4]",
        "ldrb r2, [r0, #0]",
        "lsl r2, r2, #29",
        "lsr r2, r2, #31",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #1",
        "lsr r12, r12, #1",
        "str r12, [r3, #8]",
        "ldrb r2, [r0, #0]",
        "lsl r2, r2, #28",
        "lsr r2, r2, #31",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #1",
        "lsr r12, r12, #1",
        "str r12, [r3, #12]",
        "ldrb r2, [r0, #0]",
        "lsl r2, r2, #27",
        "lsr r2, r2, #31",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #1",
        "lsr r12, r12, #1",
        "str r12, [r3, #16]",
        "ldrb r2, [r0, #0]",
        "lsl r2, r2, #26",
        "lsr r2, r2, #31",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #1",
        "lsr r12, r12, #1",
        "str r12, [r3, #20]",
        "ldrb r2, [r0, #0]",
        "lsl r2, r2, #25",
        "lsr r2, r2, #31",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #1",
        "lsr r12, r12, #1",
        "str r12, [r3, #24]",
        "ldrb r2, [r0, #0]",
        "lsl r2, r2, #24",
        "lsr r2, r2, #31",
        "add r12, r2, r2, lsl #8",
        "add r12, r12, r2, lsl #10",
        "add r12, r12, r2, lsl #11",
        "add r12, r12, #1",
        "lsr r12, r12, #1",
        "str r12, [r3, #28]",
        "add r0, r0, #1",
        "add r3, r3, #32",
        "subs r1, r1, #1",
        "bne 26b",
        "21:",
        "bx lr",
    )
}
