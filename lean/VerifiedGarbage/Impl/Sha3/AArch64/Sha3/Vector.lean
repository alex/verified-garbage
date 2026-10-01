import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.TCB.AArch64.Isa

/-
Copyright 2017-2026 The OpenSSL Project Authors. All Rights Reserved.
Licensed under the Apache License 2.0 (see LICENSE.APACHE).

Register scheduling adapted from Andy Polyakov's Keccak-f[1600] ARMv8
implementation for OpenSSL, pinned source:
https://github.com/openssl/openssl/blob/3ca9cd10b54858c5c0f60a748bf0e874ad614dc2/crypto/sha/asm/keccak1600-armv8.pl#L549-L676

Local changes: Lean instruction definitions; unrolled rounds with immediate
round constants; low64-only state representation; separately verified boundaries.
-/

namespace VG.Impl.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64

/-- Canonical state lane i resides in the low64 bits of vreg i. -/
def vreg (i : Nat) : VReg :=
  [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31].getD i .v0

/-- The five vector operations used by the register-resident round. -/
inductive Op where
  | xor (d n m : VReg)
  | eor3 (d n m a : VReg)
  | rax1 (d n m : VReg)
  | xar (d n m : VReg) (imm : Fin 64)
  | bcax (d n m a : VReg)

def Op.instr : Op → Instr
  | .xor d n m => .vop (.logic .eor d n m)
  | .eor3 d n m a => .vop (.eor3 d n m a)
  | .rax1 d n m => .vop (.rax1 d n m)
  | .xar d n m k => .vop (.xar d n m k.val)
  | .bcax d n m a => .vop (.bcax d n m a)

/-- Column parities followed by theta's five correction words. -/
def theta : List Op :=
  [
    .eor3 .v25 .v20 .v15 .v10,
    .eor3 .v26 .v21 .v16 .v11,
    .eor3 .v27 .v22 .v17 .v12,
    .eor3 .v28 .v23 .v18 .v13,
    .eor3 .v29 .v24 .v19 .v14,
    .eor3 .v25 .v25 .v5 .v0,
    .eor3 .v26 .v26 .v6 .v1,
    .eor3 .v27 .v27 .v7 .v2,
    .eor3 .v28 .v28 .v8 .v3,
    .eor3 .v29 .v29 .v9 .v4,
    .rax1 .v30 .v25 .v27,
    .rax1 .v31 .v26 .v28,
    .rax1 .v27 .v27 .v29,
    .rax1 .v28 .v28 .v25,
    .rax1 .v29 .v29 .v26]

/-- Theta addition, rotation and pi, scheduled without copying live lanes. -/
def rhoPi : List Op :=
  [
    .xar .v25 .v1 .v30 ⟨63, by decide⟩,
    .xar .v1 .v6 .v30 ⟨20, by decide⟩,
    .xar .v6 .v9 .v28 ⟨44, by decide⟩,
    .xar .v9 .v22 .v31 ⟨3, by decide⟩,
    .xar .v22 .v14 .v28 ⟨25, by decide⟩,
    .xar .v14 .v20 .v29 ⟨46, by decide⟩,
    .xar .v26 .v2 .v31 ⟨2, by decide⟩,
    .xar .v2 .v12 .v31 ⟨21, by decide⟩,
    .xar .v12 .v13 .v27 ⟨39, by decide⟩,
    .xar .v13 .v19 .v28 ⟨56, by decide⟩,
    .xar .v19 .v23 .v27 ⟨8, by decide⟩,
    .xar .v23 .v15 .v29 ⟨23, by decide⟩,
    .xar .v15 .v4 .v28 ⟨37, by decide⟩,
    .xar .v28 .v24 .v28 ⟨50, by decide⟩,
    .xar .v24 .v21 .v30 ⟨62, by decide⟩,
    .xar .v8 .v8 .v27 ⟨9, by decide⟩,
    .xar .v4 .v16 .v30 ⟨19, by decide⟩,
    .xar .v16 .v5 .v29 ⟨28, by decide⟩,
    .xar .v5 .v3 .v27 ⟨36, by decide⟩,
    .xor .v0 .v0 .v29,
    .xar .v27 .v18 .v27 ⟨43, by decide⟩,
    .xar .v3 .v17 .v31 ⟨49, by decide⟩,
    .xar .v30 .v11 .v30 ⟨54, by decide⟩,
    .xar .v31 .v7 .v31 ⟨58, by decide⟩,
    .xar .v29 .v10 .v29 ⟨61, by decide⟩]

/-- Physical register holding B[x,y] after rho/pi. -/
def breg (i : Nat) : VReg :=
  [VReg.v0, .v1, .v2, .v27, .v28, .v5, .v6, .v29, .v4, .v9,
    .v25, .v31, .v12, .v13, .v14, .v15, .v16, .v30, .v3, .v19,
    .v26, .v8, .v22, .v23, .v24].getD i .v0

/-- Chi restores canonical register allocation with no row-save moves. -/
def chi : List Op :=
  [
    .bcax .v20 .v26 .v22 .v8,
    .bcax .v21 .v8 .v23 .v22,
    .bcax .v22 .v22 .v24 .v23,
    .bcax .v23 .v23 .v26 .v24,
    .bcax .v24 .v24 .v8 .v26,
    .bcax .v17 .v30 .v19 .v3,
    .bcax .v18 .v3 .v15 .v19,
    .bcax .v19 .v19 .v16 .v15,
    .bcax .v15 .v15 .v30 .v16,
    .bcax .v16 .v16 .v3 .v30,
    .bcax .v10 .v25 .v12 .v31,
    .bcax .v11 .v31 .v13 .v12,
    .bcax .v12 .v12 .v14 .v13,
    .bcax .v13 .v13 .v25 .v14,
    .bcax .v14 .v14 .v31 .v25,
    .bcax .v7 .v29 .v9 .v4,
    .bcax .v8 .v4 .v5 .v9,
    .bcax .v9 .v9 .v6 .v5,
    .bcax .v5 .v5 .v29 .v6,
    .bcax .v6 .v6 .v4 .v29,
    .bcax .v3 .v27 .v0 .v28,
    .bcax .v4 .v28 .v1 .v0,
    .bcax .v0 .v0 .v2 .v1,
    .bcax .v1 .v1 .v27 .v2,
    .bcax .v2 .v2 .v28 .v27]

/-- Zero halfwords need no MOVK after MOVZ. The general builder also handles
halfword2, although all 24 Keccak constants have that halfword zero. -/
def constant (v : BitVec 64) : List Instr :=
  [.movz .x .x16 (v.extractLsb' 0 16) 0] ++
    (if v.extractLsb' 16 16 = 0 then [] else [.movk .x .x16 (v.extractLsb' 16 16) 1]) ++
    (if v.extractLsb' 32 16 = 0 then [] else [.movk .x .x16 (v.extractLsb' 32 16) 2]) ++
    (if v.extractLsb' 48 16 = 0 then [] else [.movk .x .x16 (v.extractLsb' 48 16) 3])

def iota : List Instr := [.vop (.dup .d2 .v26 .x16), .vop (.logic .eor .v0 .v0 .v26)]

/-- One round. Only x16 and vector registers change. -/
def round (r : Nat) : List Instr :=
  constant (Spec.Sha3.RC r) ++ theta.map Op.instr ++ rhoPi.map Op.instr ++
    chi.map Op.instr ++ iota

/-- All 24 rounds; no loads/stores and no state movement through GPRs. -/
def rounds : List Instr := (List.range 24).flatMap round

end VG.Impl.Sha3.AArch64.Sha3.Vector
