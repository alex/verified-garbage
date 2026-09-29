// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `mlkem` functions for `aarch64`.
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
        "movz x9, #3329, lsl #0",
        "movz x10, #256, lsl #0",
        "20:",
        "ldr w11, [x0, #0]",
        "ldr w12, [x1, #0]",
        "add x11, x11, x12",
        "sub x11, x11, x9",
        "lsr x13, x11, #63",
        "madd x11, x13, x9, x11",
        "str w11, [x0, #0]",
        "add x0, x0, #4",
        "add x1, x1, #4",
        "sub x10, x10, #1",
        "cbnz x10, 20b",
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
/// * Neither `f` nor `g` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_sub(f: *mut [u32; 256], g: *const [u32; 256]) {
    core::arch::naked_asm!(
        "movz x9, #3329, lsl #0",
        "movz x10, #256, lsl #0",
        "20:",
        "ldr w11, [x0, #0]",
        "ldr w12, [x1, #0]",
        "add x11, x11, x9",
        "sub x11, x11, x12",
        "sub x11, x11, x9",
        "lsr x13, x11, #63",
        "madd x11, x13, x9, x11",
        "str w11, [x0, #0]",
        "add x0, x0, #4",
        "add x1, x1, #4",
        "sub x10, x10, #1",
        "cbnz x10, 20b",
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
/// * Neither `f` nor `out` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_encode12(f: *const [u32; 256], out: *mut [u8; 384]) {
    core::arch::naked_asm!(
        "movz x13, #128, lsl #0",
        "20:",
        "ldr w9, [x0, #0]",
        "ldr w10, [x0, #4]",
        "strb w9, [x1, #0]",
        "lsr x11, x9, #8",
        "lsl x12, x10, #4",
        "add x11, x11, x12",
        "strb w11, [x1, #1]",
        "lsr x12, x10, #4",
        "strb w12, [x1, #2]",
        "add x0, x0, #8",
        "add x1, x1, #3",
        "sub x13, x13, #1",
        "cbnz x13, 20b",
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
/// * Neither `b` nor `f` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_decode12(b: *const [u8; 384], f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "movz x14, #15, lsl #0",
        "movz x15, #3329, lsl #0",
        "movz x16, #128, lsl #0",
        "20:",
        "ldrb w9, [x0, #0]",
        "ldrb w10, [x0, #1]",
        "ldrb w11, [x0, #2]",
        "and x12, x10, x14",
        "lsl x12, x12, #8",
        "add x12, x12, x9",
        "sub x12, x12, x15",
        "lsr x13, x12, #63",
        "madd x12, x13, x15, x12",
        "str w12, [x1, #0]",
        "lsr x12, x10, #4",
        "lsl x13, x11, #4",
        "add x12, x12, x13",
        "sub x12, x12, x15",
        "lsr x13, x12, #63",
        "madd x12, x13, x15, x12",
        "str w12, [x1, #4]",
        "add x0, x0, #3",
        "add x1, x1, #8",
        "sub x16, x16, #1",
        "cbnz x16, 20b",
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
/// * Neither `b` nor `f` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_cbd2(b: *const [u8; 128], f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "movz x14, #85, lsl #0",
        "movz x15, #3, lsl #0",
        "movz x12, #3329, lsl #0",
        "movz x16, #128, lsl #0",
        "20:",
        "ldrb w9, [x0, #0]",
        "lsr x10, x9, #1",
        "and x9, x9, x14",
        "and x10, x10, x14",
        "add x9, x9, x10",
        "and x10, x9, x15",
        "lsr x11, x9, #2",
        "and x11, x11, x15",
        "add x10, x10, x12",
        "sub x10, x10, x11",
        "sub x10, x10, x12",
        "lsr x13, x10, #63",
        "madd x10, x13, x12, x10",
        "str w10, [x1, #0]",
        "lsr x10, x9, #4",
        "and x10, x10, x15",
        "lsr x11, x9, #6",
        "add x10, x10, x12",
        "sub x10, x10, x11",
        "sub x10, x10, x12",
        "lsr x13, x10, #63",
        "madd x10, x13, x12, x10",
        "str w10, [x1, #4]",
        "add x0, x0, #1",
        "add x1, x1, #8",
        "sub x16, x16, #1",
        "cbnz x16, 20b",
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
/// * Neither `f` nor `out` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_compress_encode(f: *const [u32; 256], d: u32, out: *mut u8, len: usize) {
    core::arch::naked_asm!(
        "movz x6, #65472, lsl #0",
        "movk x6, #3, lsl #16",
        "movk x6, #0, lsl #32",
        "movk x6, #0, lsl #48",
        "sub x9, x3, #32",
        "cbz x9, 20f",
        "sub x9, x3, #128",
        "cbz x9, 22f",
        "movz x5, #30199, lsl #0",
        "movk x5, #2, lsl #16",
        "movk x5, #0, lsl #32",
        "movk x5, #0, lsl #48",
        "movz x7, #1023, lsl #0",
        "movk x7, #0, lsl #16",
        "movk x7, #0, lsl #32",
        "movk x7, #0, lsl #48",
        "movz x11, #64, lsl #0",
        "movk x11, #0, lsl #16",
        "movk x11, #0, lsl #32",
        "movk x11, #0, lsl #48",
        "24:",
        "movz x9, #0, lsl #0",
        "ldr w10, [x0, #0]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #0",
        "add x9, x9, x10",
        "ldr w10, [x0, #4]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #10",
        "add x9, x9, x10",
        "ldr w10, [x0, #8]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #20",
        "add x9, x9, x10",
        "ldr w10, [x0, #12]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #30",
        "add x9, x9, x10",
        "lsr x10, x9, #0",
        "strb w10, [x2, #0]",
        "lsr x10, x9, #8",
        "strb w10, [x2, #1]",
        "lsr x10, x9, #16",
        "strb w10, [x2, #2]",
        "lsr x10, x9, #24",
        "strb w10, [x2, #3]",
        "lsr x10, x9, #32",
        "strb w10, [x2, #4]",
        "add x0, x0, #16",
        "add x2, x2, #5",
        "sub x11, x11, #1",
        "cbnz x11, 24b",
        "b 23f",
        "22:",
        "movz x5, #2520, lsl #0",
        "movk x5, #0, lsl #16",
        "movk x5, #0, lsl #32",
        "movk x5, #0, lsl #48",
        "movz x7, #15, lsl #0",
        "movk x7, #0, lsl #16",
        "movk x7, #0, lsl #32",
        "movk x7, #0, lsl #48",
        "movz x11, #128, lsl #0",
        "movk x11, #0, lsl #16",
        "movk x11, #0, lsl #32",
        "movk x11, #0, lsl #48",
        "25:",
        "movz x9, #0, lsl #0",
        "ldr w10, [x0, #0]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #0",
        "add x9, x9, x10",
        "ldr w10, [x0, #4]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #4",
        "add x9, x9, x10",
        "lsr x10, x9, #0",
        "strb w10, [x2, #0]",
        "add x0, x0, #8",
        "add x2, x2, #1",
        "sub x11, x11, #1",
        "cbnz x11, 25b",
        "23:",
        "b 21f",
        "20:",
        "movz x5, #315, lsl #0",
        "movk x5, #0, lsl #16",
        "movk x5, #0, lsl #32",
        "movk x5, #0, lsl #48",
        "movz x7, #1, lsl #0",
        "movk x7, #0, lsl #16",
        "movk x7, #0, lsl #32",
        "movk x7, #0, lsl #48",
        "movz x11, #32, lsl #0",
        "movk x11, #0, lsl #16",
        "movk x11, #0, lsl #32",
        "movk x11, #0, lsl #48",
        "26:",
        "movz x9, #0, lsl #0",
        "ldr w10, [x0, #0]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #0",
        "add x9, x9, x10",
        "ldr w10, [x0, #4]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #1",
        "add x9, x9, x10",
        "ldr w10, [x0, #8]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #2",
        "add x9, x9, x10",
        "ldr w10, [x0, #12]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #3",
        "add x9, x9, x10",
        "ldr w10, [x0, #16]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #4",
        "add x9, x9, x10",
        "ldr w10, [x0, #20]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #5",
        "add x9, x9, x10",
        "ldr w10, [x0, #24]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #6",
        "add x9, x9, x10",
        "ldr w10, [x0, #28]",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #19",
        "and x10, x10, x7",
        "lsl x10, x10, #7",
        "add x9, x9, x10",
        "lsr x10, x9, #0",
        "strb w10, [x2, #0]",
        "add x0, x0, #32",
        "add x2, x2, #1",
        "sub x11, x11, #1",
        "cbnz x11, 26b",
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
/// * Neither `b` nor `f` may wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_mlkem_decode_decompress(b: *const u8, len: usize, d: u32, f: *mut [u32; 256]) {
    core::arch::naked_asm!(
        "movz x5, #3329, lsl #0",
        "movk x5, #0, lsl #16",
        "movk x5, #0, lsl #32",
        "movk x5, #0, lsl #48",
        "sub x9, x1, #32",
        "cbz x9, 20f",
        "sub x9, x1, #128",
        "cbz x9, 22f",
        "movz x6, #512, lsl #0",
        "movk x6, #0, lsl #16",
        "movk x6, #0, lsl #32",
        "movk x6, #0, lsl #48",
        "movz x7, #1023, lsl #0",
        "movk x7, #0, lsl #16",
        "movk x7, #0, lsl #32",
        "movk x7, #0, lsl #48",
        "movz x11, #64, lsl #0",
        "movk x11, #0, lsl #16",
        "movk x11, #0, lsl #32",
        "movk x11, #0, lsl #48",
        "24:",
        "movz x9, #0, lsl #0",
        "ldrb w10, [x0, #0]",
        "lsl x10, x10, #0",
        "add x9, x9, x10",
        "ldrb w10, [x0, #1]",
        "lsl x10, x10, #8",
        "add x9, x9, x10",
        "ldrb w10, [x0, #2]",
        "lsl x10, x10, #16",
        "add x9, x9, x10",
        "ldrb w10, [x0, #3]",
        "lsl x10, x10, #24",
        "add x9, x9, x10",
        "ldrb w10, [x0, #4]",
        "lsl x10, x10, #32",
        "add x9, x9, x10",
        "lsr x10, x9, #0",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #10",
        "str w10, [x3, #0]",
        "lsr x10, x9, #10",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #10",
        "str w10, [x3, #4]",
        "lsr x10, x9, #20",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #10",
        "str w10, [x3, #8]",
        "lsr x10, x9, #30",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #10",
        "str w10, [x3, #12]",
        "add x0, x0, #5",
        "add x3, x3, #16",
        "sub x11, x11, #1",
        "cbnz x11, 24b",
        "b 23f",
        "22:",
        "movz x6, #8, lsl #0",
        "movk x6, #0, lsl #16",
        "movk x6, #0, lsl #32",
        "movk x6, #0, lsl #48",
        "movz x7, #15, lsl #0",
        "movk x7, #0, lsl #16",
        "movk x7, #0, lsl #32",
        "movk x7, #0, lsl #48",
        "movz x11, #128, lsl #0",
        "movk x11, #0, lsl #16",
        "movk x11, #0, lsl #32",
        "movk x11, #0, lsl #48",
        "25:",
        "movz x9, #0, lsl #0",
        "ldrb w10, [x0, #0]",
        "lsl x10, x10, #0",
        "add x9, x9, x10",
        "lsr x10, x9, #0",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #4",
        "str w10, [x3, #0]",
        "lsr x10, x9, #4",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #4",
        "str w10, [x3, #4]",
        "add x0, x0, #1",
        "add x3, x3, #8",
        "sub x11, x11, #1",
        "cbnz x11, 25b",
        "23:",
        "b 21f",
        "20:",
        "movz x6, #1, lsl #0",
        "movk x6, #0, lsl #16",
        "movk x6, #0, lsl #32",
        "movk x6, #0, lsl #48",
        "movz x7, #1, lsl #0",
        "movk x7, #0, lsl #16",
        "movk x7, #0, lsl #32",
        "movk x7, #0, lsl #48",
        "movz x11, #32, lsl #0",
        "movk x11, #0, lsl #16",
        "movk x11, #0, lsl #32",
        "movk x11, #0, lsl #48",
        "26:",
        "movz x9, #0, lsl #0",
        "ldrb w10, [x0, #0]",
        "lsl x10, x10, #0",
        "add x9, x9, x10",
        "lsr x10, x9, #0",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #1",
        "str w10, [x3, #0]",
        "lsr x10, x9, #1",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #1",
        "str w10, [x3, #4]",
        "lsr x10, x9, #2",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #1",
        "str w10, [x3, #8]",
        "lsr x10, x9, #3",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #1",
        "str w10, [x3, #12]",
        "lsr x10, x9, #4",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #1",
        "str w10, [x3, #16]",
        "lsr x10, x9, #5",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #1",
        "str w10, [x3, #20]",
        "lsr x10, x9, #6",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #1",
        "str w10, [x3, #24]",
        "lsr x10, x9, #7",
        "and x10, x10, x7",
        "mul x10, x10, x5",
        "add x10, x10, x6",
        "lsr x10, x10, #1",
        "str w10, [x3, #28]",
        "add x0, x0, #1",
        "add x3, x3, #32",
        "sub x11, x11, #1",
        "cbnz x11, 26b",
        "21:",
        "ret",
    )
}
