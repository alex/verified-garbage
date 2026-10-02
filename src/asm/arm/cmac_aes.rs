// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.
//! Verified `cmac_aes` functions for `arm`.
#![allow(dead_code)]

/// The CMAC subkey generation (NIST SP 800-38B §6.1) for AES: writes `K1 ‖ K2` to `*subkeys`, where `L = CIPH_K(0¹²⁸)`, `K1 = L << 1` (XORed with `R₁₂₈ = 0¹²⁰10000111` if the leftmost bit of `L` is 1) and `K2` is `K1` doubled the same way. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it.
///
/// Contract: `VG.Spec.Cmac.aesSubkeysContract`. Constant time: only the pointers and `rounds` may affect timing, not the key schedule or the subkeys.
///
/// This implementation encrypts each block with `vg_aes_ctr32`.
///
/// # Safety
///
/// * `schedule` must be valid for reads of 240 bytes.
/// * `subkeys` must be valid for reads and writes of 32 bytes.
/// * `scratch` must be valid for reads and writes of 2176 bytes.
/// * `rounds` must be 10, 12 or 14.
/// * The contents of `scratch` on return are unspecified.
/// * `subkeys` and `scratch` must not overlap each other or `schedule` (distinct Rust objects never do).
/// * None of `schedule`, `subkeys` and `scratch` may overlap the 8 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_cmac_aes_subkeys(schedule: *const [u8; 240], rounds: usize, subkeys: *mut [u8; 32], scratch: *mut [u64; 272]) {
    core::arch::naked_asm!(
        "str r4, [r3, #2064]",
        "str r5, [r3, #2068]",
        "str r6, [r3, #2072]",
        "str lr, [r3, #2076]",
        "mov r6, r2",
        "mov r5, r3",
        "mov r12, #0",
        "str r12, [r3, #2048]",
        "str r12, [r3, #2052]",
        "str r12, [r3, #2056]",
        "str r12, [r3, #2060]",
        "str r12, [r2, #0]",
        "str r12, [r2, #4]",
        "str r12, [r2, #8]",
        "str r12, [r2, #12]",
        "add r2, r5, #2048",
        "mov r3, r6",
        "mov r4, #1",
        "push {{r4, r5}}",
        "bl {vg_aes_ctr32}",
        "ldr r4, [sp], #8",
        "ldr r0, [r6, #0]",
        "ldr r1, [r6, #4]",
        "ldr r2, [r6, #8]",
        "ldr r3, [r6, #12]",
        "rev r0, r0",
        "rev r1, r1",
        "rev r2, r2",
        "rev r3, r3",
        "lsr r12, r0, #31",
        "mov r4, #0",
        "sub r12, r4, r12",
        "and r12, r12, #135",
        "lsl r0, r0, #1",
        "orr r0, r0, r1, lsr #31",
        "lsl r1, r1, #1",
        "orr r1, r1, r2, lsr #31",
        "lsl r2, r2, #1",
        "orr r2, r2, r3, lsr #31",
        "lsl r3, r3, #1",
        "eor r3, r3, r12",
        "rev r0, r0",
        "rev r1, r1",
        "rev r2, r2",
        "rev r3, r3",
        "str r0, [r6, #0]",
        "str r1, [r6, #4]",
        "str r2, [r6, #8]",
        "str r3, [r6, #12]",
        "ldr r0, [r6, #0]",
        "ldr r1, [r6, #4]",
        "ldr r2, [r6, #8]",
        "ldr r3, [r6, #12]",
        "rev r0, r0",
        "rev r1, r1",
        "rev r2, r2",
        "rev r3, r3",
        "lsr r12, r0, #31",
        "mov r4, #0",
        "sub r12, r4, r12",
        "and r12, r12, #135",
        "lsl r0, r0, #1",
        "orr r0, r0, r1, lsr #31",
        "lsl r1, r1, #1",
        "orr r1, r1, r2, lsr #31",
        "lsl r2, r2, #1",
        "orr r2, r2, r3, lsr #31",
        "lsl r3, r3, #1",
        "eor r3, r3, r12",
        "rev r0, r0",
        "rev r1, r1",
        "rev r2, r2",
        "rev r3, r3",
        "str r0, [r6, #16]",
        "str r1, [r6, #20]",
        "str r2, [r6, #24]",
        "str r3, [r6, #28]",
        "ldr r4, [r5, #2064]",
        "ldr r6, [r5, #2072]",
        "ldr lr, [r5, #2076]",
        "ldr r5, [r5, #2068]",
        "bx lr",
        vg_aes_ctr32 = sym super::aes::vg_aes_ctr32,
    )
}

/// CMAC's chaining (NIST SP 800-38B §6.2 step 6) for AES, over whole blocks: replaces the block `C₀` at `*state` with `Cₙ`, where `Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)` for the `n` 16-byte blocks `M₁ … Mₙ` starting at `data`. `CIPH_K` is AES (FIPS 197) with `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` bytes of `*schedule`, as `vg_aes_expand_key` writes it.
///
/// Contract: `VG.Spec.Cmac.aesUpdateContract`. Constant time: only the pointers, `rounds` and `n` may affect timing, not the key schedule, the chaining value or the data.
///
/// This implementation encrypts each block with `vg_aes_ctr32`.
///
/// # Safety
///
/// * `schedule` must be valid for reads of 240 bytes.
/// * `state` must be valid for reads and writes of 16 bytes.
/// * `data` must be valid for reads of `16 * n` bytes.
/// * `scratch` must be valid for reads and writes of 2176 bytes.
/// * `rounds` must be 10, 12 or 14.
/// * The contents of `scratch` on return are unspecified.
/// * `state` and `scratch` must not overlap each other, `schedule`, `data` or the arguments on the stack (distinct Rust objects never do).
/// * None of `schedule`, `state`, `data` and `scratch` may overlap the 8 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_cmac_aes_update(schedule: *const [u8; 240], rounds: usize, state: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 272]) {
    core::arch::naked_asm!(
        "ldr r12, [sp, #4]",
        "str r4, [r12, #2064]",
        "str r5, [r12, #2068]",
        "str r6, [r12, #2072]",
        "str r7, [r12, #2076]",
        "str r8, [r12, #2080]",
        "str r9, [r12, #2084]",
        "str lr, [r12, #2092]",
        "str r10, [r12, #2088]",
        "mov r4, r0",
        "mov r5, r1",
        "mov r6, r2",
        "mov r7, r3",
        "ldr r8, [sp, #0]",
        "mov r10, r12",
        "cmp r8, #0",
        "beq 20f",
        "22:",
        "ldr r0, [r6, #0]",
        "ldr r1, [r7, #0]",
        "eor r0, r0, r1",
        "str r0, [r10, #2048]",
        "ldr r0, [r6, #4]",
        "ldr r1, [r7, #4]",
        "eor r0, r0, r1",
        "str r0, [r10, #2052]",
        "ldr r0, [r6, #8]",
        "ldr r1, [r7, #8]",
        "eor r0, r0, r1",
        "str r0, [r10, #2056]",
        "ldr r0, [r6, #12]",
        "ldr r1, [r7, #12]",
        "eor r0, r0, r1",
        "str r0, [r10, #2060]",
        "mov r0, #0",
        "str r0, [r6, #0]",
        "str r0, [r6, #4]",
        "str r0, [r6, #8]",
        "str r0, [r6, #12]",
        "mov r0, r4",
        "mov r1, r5",
        "add r2, r10, #2048",
        "mov r3, r6",
        "mov r9, #1",
        "push {{r9, r10}}",
        "bl {vg_aes_ctr32}",
        "ldr r9, [sp], #8",
        "add r7, r7, #16",
        "subs r8, r8, #1",
        "bne 22b",
        "b 21f",
        "20:",
        "21:",
        "ldr r4, [r10, #2064]",
        "ldr r5, [r10, #2068]",
        "ldr r6, [r10, #2072]",
        "ldr r7, [r10, #2076]",
        "ldr r8, [r10, #2080]",
        "ldr r9, [r10, #2084]",
        "ldr lr, [r10, #2092]",
        "ldr r10, [r10, #2088]",
        "bx lr",
        vg_aes_ctr32 = sym super::aes::vg_aes_ctr32,
    )
}

/// Finishes an AES-CMAC computation (NIST SP 800-38B §6.2, with `Tlen = 128`): if the block at `*state` is the chaining value `Cₙ₋₁` of the message's blocks but the last (as `vg_cmac_aes_update` computes it from a zero block), and the `last_len` bytes at `last` are the message's last bytes `Mₙ*`, replaces it with the MAC `Cₙ = CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, where `Mₙ = K1 ⊕ Mₙ*` if `last_len` is 16, and `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` otherwise. `*key` is the 240 bytes `vg_aes_expand_key` writes the key schedule for `rounds` rounds to, followed by the subkeys `K1 ‖ K2` (as `vg_cmac_aes_subkeys` writes them). `last_len` is 0 only for the empty message.
///
/// Contract: `VG.Spec.Cmac.aesFinalizeContract`. Constant time: only the pointers, `rounds` and `last_len` may affect timing, not the key schedule, the subkeys, the chaining value or the data.
///
/// This implementation encrypts each block with `vg_aes_ctr32`.
///
/// # Safety
///
/// * `key` must be valid for reads of 272 bytes.
/// * `state` must be valid for reads and writes of 16 bytes.
/// * `last` must be valid for reads of `last_len` bytes.
/// * `scratch` must be valid for reads and writes of 2176 bytes.
/// * `rounds` must be 10, 12 or 14.
/// * `last_len` must be at most 16.
/// * The contents of `scratch` on return are unspecified.
/// * `state` and `scratch` must not overlap each other, `key`, `last` or the arguments on the stack (distinct Rust objects never do).
/// * None of `key`, `state`, `last` and `scratch` may overlap the 8 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_cmac_aes_finalize(key: *const [u8; 272], rounds: usize, state: *mut [u8; 16], last: *const u8, last_len: usize, scratch: *mut [u64; 272]) {
    core::arch::naked_asm!(
        "ldr r12, [sp, #4]",
        "str r4, [r12, #2064]",
        "str r5, [r12, #2068]",
        "str lr, [r12, #2072]",
        "mov r5, r12",
        "ldr r4, [sp, #0]",
        "cmp r4, #16",
        "beq 20f",
        "mov r12, #0",
        "str r12, [r5, #2048]",
        "str r12, [r5, #2052]",
        "str r12, [r5, #2056]",
        "str r12, [r5, #2060]",
        "add lr, r5, #2048",
        "cmp r4, #0",
        "beq 22f",
        "24:",
        "ldrb r12, [r3, #0]",
        "strb r12, [lr, #0]",
        "add r3, r3, #1",
        "add lr, lr, #1",
        "subs r4, r4, #1",
        "bne 24b",
        "b 23f",
        "22:",
        "23:",
        "mov r12, #128",
        "strb r12, [lr, #0]",
        "ldr r12, [r5, #2048]",
        "ldr lr, [r0, #256]",
        "eor r12, r12, lr",
        "str r12, [r5, #2048]",
        "ldr r12, [r5, #2052]",
        "ldr lr, [r0, #260]",
        "eor r12, r12, lr",
        "str r12, [r5, #2052]",
        "ldr r12, [r5, #2056]",
        "ldr lr, [r0, #264]",
        "eor r12, r12, lr",
        "str r12, [r5, #2056]",
        "ldr r12, [r5, #2060]",
        "ldr lr, [r0, #268]",
        "eor r12, r12, lr",
        "str r12, [r5, #2060]",
        "b 21f",
        "20:",
        "ldr r12, [r3, #0]",
        "ldr lr, [r0, #240]",
        "eor r12, r12, lr",
        "str r12, [r5, #2048]",
        "ldr r12, [r3, #4]",
        "ldr lr, [r0, #244]",
        "eor r12, r12, lr",
        "str r12, [r5, #2052]",
        "ldr r12, [r3, #8]",
        "ldr lr, [r0, #248]",
        "eor r12, r12, lr",
        "str r12, [r5, #2056]",
        "ldr r12, [r3, #12]",
        "ldr lr, [r0, #252]",
        "eor r12, r12, lr",
        "str r12, [r5, #2060]",
        "21:",
        "ldr r12, [r5, #2048]",
        "ldr lr, [r2, #0]",
        "eor r12, r12, lr",
        "str r12, [r5, #2048]",
        "ldr r12, [r5, #2052]",
        "ldr lr, [r2, #4]",
        "eor r12, r12, lr",
        "str r12, [r5, #2052]",
        "ldr r12, [r5, #2056]",
        "ldr lr, [r2, #8]",
        "eor r12, r12, lr",
        "str r12, [r5, #2056]",
        "ldr r12, [r5, #2060]",
        "ldr lr, [r2, #12]",
        "eor r12, r12, lr",
        "str r12, [r5, #2060]",
        "mov r12, #0",
        "str r12, [r2, #0]",
        "str r12, [r2, #4]",
        "str r12, [r2, #8]",
        "str r12, [r2, #12]",
        "mov r3, r2",
        "add r2, r5, #2048",
        "mov r4, #1",
        "push {{r4, r5}}",
        "bl {vg_aes_ctr32}",
        "ldr r4, [sp], #8",
        "ldr r4, [r5, #2064]",
        "ldr lr, [r5, #2072]",
        "ldr r5, [r5, #2068]",
        "bx lr",
        vg_aes_ctr32 = sym super::aes::vg_aes_ctr32,
    )
}

/// Starts an AES-CMAC computation (NIST SP 800-38B, RFC 4493): makes the streaming state `*state` represent the empty message under the AES key of `key_len` bytes at `key` (AES-128, AES-192 or AES-256). The state holds the key schedule of AES (FIPS 197) with `key_len / 4 + 6` rounds, the subkeys `K1 ‖ K2` (§6.1), the chaining value and the message's last bytes, held back (`VG.Spec.Cmac.Repr`). Continue with `vg_cmac_aes_absorb` and `vg_cmac_aes_finish`, passing them `key_len / 4 + 6` as `rounds`.
///
/// Contract: `VG.Spec.Cmac.aesInitContract`. Constant time: only the pointers and `key_len` may affect timing, not the key.
///
/// This implementation expands the key with `vg_aes_expand_key` and derives the subkeys with `vg_cmac_aes_subkeys`.
///
/// # Safety
///
/// * `state` must be valid for reads and writes of 304 bytes.
/// * `key` must be valid for reads of `key_len` bytes.
/// * `scratch` must be valid for reads and writes of 2304 bytes.
/// * `key_len` must be 16, 24 or 32.
/// * The contents of `scratch` on return are unspecified.
/// * `state` and `scratch` must not overlap each other or `key` (distinct Rust objects never do).
/// * None of `state`, `key` and `scratch` may overlap the 8 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_cmac_aes_init(state: *mut [u64; 38], key: *const u8, key_len: usize, scratch: *mut [u64; 288]) {
    core::arch::naked_asm!(
        "str r4, [r3, #2176]",
        "str r5, [r3, #2180]",
        "str r6, [r3, #2184]",
        "str lr, [r3, #2188]",
        "mov r4, r0",
        "mov r5, r3",
        "lsr r6, r2, #2",
        "add r6, r6, #6",
        "mov r0, r1",
        "mov r1, r2",
        "mov r2, r4",
        "bl {vg_aes_expand_key}",
        "mov r0, r4",
        "mov r1, r6",
        "add r2, r4, #240",
        "mov r3, r5",
        "bl {vg_cmac_aes_subkeys}",
        "mov r12, #0",
        "str r12, [r4, #272]",
        "str r12, [r4, #276]",
        "str r12, [r4, #280]",
        "str r12, [r4, #284]",
        "ldr r4, [r5, #2176]",
        "ldr r6, [r5, #2184]",
        "ldr lr, [r5, #2188]",
        "ldr r5, [r5, #2180]",
        "bx lr",
        vg_aes_expand_key = sym super::aes::vg_aes_expand_key,
        vg_cmac_aes_subkeys = sym super::cmac_aes::vg_cmac_aes_subkeys,
    )
}

/// Absorbs data into an AES-CMAC computation (NIST SP 800-38B §6.2): if the streaming state `*state` represents a message of `count` bytes under an AES key with `rounds` rounds (as `vg_cmac_aes_init` set it up), it then represents that message followed by the `len` bytes at `data`, under the same key, provided that the two together are shorter than 2⁶⁴ bytes. It chains (step 6) every block of the message but its last bytes `Mₙ*` (step 3), which it holds back in the state, since only `vg_cmac_aes_finish` knows they are the last.
///
/// Contract: `VG.Spec.Cmac.aesAbsorbContract`. Constant time: only the pointers, `rounds`, `count` and `len` may affect timing, not the state or the data.
///
/// This implementation chains the blocks with `vg_cmac_aes_update`.
///
/// # Safety
///
/// * `state` must be valid for reads and writes of 304 bytes.
/// * `data` must be valid for reads of `len` bytes.
/// * `scratch` must be valid for reads and writes of 2304 bytes.
/// * `rounds` must be 10, 12 or 14.
/// * The contents of `scratch` on return are unspecified.
/// * `state` and `scratch` must not overlap each other, `data` or the arguments on the stack (distinct Rust objects never do).
/// * None of `state`, `data` and `scratch` may overlap the 16 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_cmac_aes_absorb(state: *mut [u64; 38], rounds: usize, count: u64, data: *const u8, len: usize, scratch: *mut [u64; 288]) {
    core::arch::naked_asm!(
        "ldr r12, [sp, #8]",
        "str r4, [r12, #2176]",
        "str r5, [r12, #2180]",
        "str r6, [r12, #2184]",
        "str r7, [r12, #2188]",
        "str r8, [r12, #2192]",
        "str r9, [r12, #2196]",
        "str lr, [r12, #2204]",
        "str r10, [r12, #2200]",
        "mov r4, r0",
        "mov r5, r1",
        "ldr r6, [sp, #0]",
        "ldr r7, [sp, #4]",
        "mov r10, r12",
        "sub r0, r2, #1",
        "and r0, r0, #15",
        "add r0, r0, #1",
        "orr r12, r2, r3",
        "cmp r12, #0",
        "beq 20f",
        "b 21f",
        "20:",
        "mov r0, #0",
        "21:",
        "mov r1, #16",
        "sub r1, r1, r0",
        "lsr r12, r7, #4",
        "cmp r12, #0",
        "beq 22f",
        "b 23f",
        "22:",
        "add r12, r7, r0",
        "lsr r12, r12, #4",
        "cmp r12, #0",
        "beq 24f",
        "b 25f",
        "24:",
        "mov r1, r7",
        "25:",
        "23:",
        "add r2, r4, r0",
        "add r2, r2, #288",
        "sub r7, r7, r1",
        "cmp r1, #0",
        "beq 26f",
        "28:",
        "ldrb r12, [r6, #0]",
        "strb r12, [r2, #0]",
        "add r6, r6, #1",
        "add r2, r2, #1",
        "subs r1, r1, #1",
        "bne 28b",
        "b 27f",
        "26:",
        "27:",
        "mov r9, #0",
        "cmp r7, #0",
        "beq 29f",
        "mov r9, #1",
        "b 210f",
        "29:",
        "210:",
        "mov r0, r4",
        "mov r1, r5",
        "add r2, r4, #272",
        "add r3, r4, #288",
        "push {{r9, r10}}",
        "bl {vg_cmac_aes_update}",
        "ldr r9, [sp], #8",
        "cmp r7, #0",
        "beq 211f",
        "sub r9, r7, #1",
        "lsr r9, r9, #4",
        "lsl r8, r9, #4",
        "mov r3, r6",
        "b 212f",
        "211:",
        "mov r9, #0",
        "mov r8, #0",
        "mov r3, r4",
        "212:",
        "mov r0, r4",
        "mov r1, r5",
        "add r2, r4, #272",
        "push {{r9, r10}}",
        "bl {vg_cmac_aes_update}",
        "ldr r9, [sp], #8",
        "add r6, r6, r8",
        "sub r7, r7, r8",
        "mov r1, r7",
        "add r2, r4, #288",
        "sub r7, r7, r1",
        "cmp r1, #0",
        "beq 213f",
        "215:",
        "ldrb r12, [r6, #0]",
        "strb r12, [r2, #0]",
        "add r6, r6, #1",
        "add r2, r2, #1",
        "subs r1, r1, #1",
        "bne 215b",
        "b 214f",
        "213:",
        "214:",
        "ldr r4, [r10, #2176]",
        "ldr r5, [r10, #2180]",
        "ldr r6, [r10, #2184]",
        "ldr r7, [r10, #2188]",
        "ldr r8, [r10, #2192]",
        "ldr r9, [r10, #2196]",
        "ldr lr, [r10, #2204]",
        "ldr r10, [r10, #2200]",
        "bx lr",
        vg_cmac_aes_update = sym super::cmac_aes::vg_cmac_aes_update,
    )
}

/// Finishes an AES-CMAC computation (NIST SP 800-38B §6.2, with `Tlen = 128`): if the streaming state `*state` represents a message of `count` bytes, shorter than 2⁶⁴ bytes, under an AES key with `rounds` rounds (as `vg_cmac_aes_init` and `vg_cmac_aes_absorb` set it up), writes the MAC of that message under that key to `*out`: `Cₙ = CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, where `Mₙ = K1 ⊕ Mₙ*` if the message's last bytes `Mₙ*` are a complete block, and `Mₙ = K2 ⊕ (Mₙ* ‖ 10ʲ)` otherwise (step 4). The caller truncates it (step 7) and compares it (§6.3).
///
/// Contract: `VG.Spec.Cmac.aesFinishContract`. Constant time: only the pointers, `rounds` and `count` may affect timing, not the state.
///
/// This implementation computes the MAC with `vg_cmac_aes_finalize`.
///
/// # Safety
///
/// * `state` must be valid for reads and writes of 304 bytes.
/// * `out` must be valid for reads and writes of 16 bytes.
/// * `scratch` must be valid for reads and writes of 2304 bytes.
/// * `rounds` must be 10, 12 or 14.
/// * The contents of `state` on return are unspecified.
/// * The contents of `scratch` on return are unspecified.
/// * `state`, `out` and `scratch` must not overlap each other or the arguments on the stack (distinct Rust objects never do).
/// * None of `state`, `out` and `scratch` may overlap the 16 bytes of stack below the stack pointer, or wrap around the end of the address space (no Rust object does).
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_cmac_aes_finish(state: *mut [u64; 38], rounds: usize, count: u64, out: *mut [u8; 16], scratch: *mut [u64; 288]) {
    core::arch::naked_asm!(
        "ldr r12, [sp, #4]",
        "str r4, [r12, #2176]",
        "str r5, [r12, #2180]",
        "str lr, [r12, #2184]",
        "mov r5, r12",
        "ldr r12, [sp, #0]",
        "ldr lr, [r0, #272]",
        "str lr, [r12, #0]",
        "ldr lr, [r0, #276]",
        "str lr, [r12, #4]",
        "ldr lr, [r0, #280]",
        "str lr, [r12, #8]",
        "ldr lr, [r0, #284]",
        "str lr, [r12, #12]",
        "sub r4, r2, #1",
        "and r4, r4, #15",
        "add r4, r4, #1",
        "orr r2, r2, r3",
        "cmp r2, #0",
        "beq 20f",
        "b 21f",
        "20:",
        "mov r4, #0",
        "21:",
        "mov r2, r12",
        "add r3, r0, #288",
        "push {{r4, r5}}",
        "bl {vg_cmac_aes_finalize}",
        "ldr r4, [sp], #8",
        "ldr r4, [r5, #2176]",
        "ldr lr, [r5, #2184]",
        "ldr r5, [r5, #2180]",
        "bx lr",
        vg_cmac_aes_finalize = sym super::cmac_aes::vg_cmac_aes_finalize,
    )
}
