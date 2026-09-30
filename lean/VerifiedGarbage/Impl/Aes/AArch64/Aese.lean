import VerifiedGarbage.TCB.AArch64.Isa

/-!
# AES with the Armv8 Cryptographic Extension: GCM's counter mode

`vg_aes_ctr32_aes(schedule = x0, rounds = x1, counter = x2, data = x3, n = x4, scratch = x5)`,
with the contract of `vg_aes_ctr32` (`Spec.Gcm.ctr32Contract`), for CPUs with
FEAT_AES. It does not use `scratch`, and writes no callee-saved register.
Every branch and every address depends only on the pointers and the public
lengths (`rounds`, `n`).

A vector register holds an AES state as its 16 bytes in memory order, as the
cryptographic instructions read it. `aese b, k` is `SubBytes(ShiftRows(b ⊕ k))`
and `aesmc b, b` is `MixColumns(b)`, so a full round with round key `j` is
`aese b, k_j; aesmc b, b` (whose `⊕ k_j` is the previous round's
`AddRoundKey`), and the last two rounds `aese b, k_{Nr−1}; eor b, b, k_Nr`.
Each `aese` is followed by its `aesmc`, which cores fuse.

* The round keys stay in registers: `k₀ … k₈` in `v16`–`v24`, `k₉ … k₁₂` in
  `v25`–`v28` (loaded whatever the key size: they are in the 240-byte
  schedule, and only used for 12 or 14 rounds), `k_{Nr−1}` in `v29` and
  `k_Nr` in `v30`.
* `x6 = rounds − 10` and `x7 = rounds − 12` choose the rounds with `k₉ … k₁₂`.
* The counter `int(LSB₃₂(CB))` is kept in `w10`; counter block `i` of a
  group is the counter block loaded from `counter` with its last word
  replaced by `rev(w10 + i)`.
* Eight blocks at a time (`v0`–`v7`), each round applied to all eight so the
  AES pipeline stays full, then one at a time; `v31` holds the data block
  being XORed. The final counter is written back at the end.
-/

namespace VG.Impl.Aes.AArch64.Aese

open VG.AArch64

/-- The register of round key `j`, for the full rounds (`j ≤ 12`). -/
def kreg : Nat → VReg
  | 0 => .v16 | 1 => .v17 | 2 => .v18 | 3 => .v19 | 4 => .v20 | 5 => .v21 | 6 => .v22
  | 7 => .v23 | 8 => .v24 | 9 => .v25 | 10 => .v26 | 11 => .v27 | _ => .v28

/-- A full round with the round key in `k`, of each block register. -/
def rnd (regs : List VReg) (k : VReg) : List Instr :=
  regs.flatMap fun b => [.vop (.aese b k), .vop (.aesmc b b)]

/-- The last round (`aese` with `k_{Nr−1}`, then `AddRoundKey` with `k_Nr`). -/
def last (regs : List VReg) : List Instr :=
  regs.flatMap fun b => [.vop (.aese b .v29), .vop (.logic .eor b b .v30)]

/-- AES of each block register: the full rounds with `k₀ … k₈`, then with
`k₉, k₁₀` unless `rounds = 10` and `k₁₁, k₁₂` unless `rounds = 12` too, and the
last. -/
def aes (regs : List VReg) : Prog isa :=
  .seq (.block ((List.range 9).flatMap fun j => rnd regs (kreg j)))
    (.seq (.ite (.zero .x .x6) (.block [])
        (.seq (.block (rnd regs .v25 ++ rnd regs .v26))
          (.ite (.zero .x .x7) (.block []) (.block (rnd regs .v27 ++ rnd regs .v28)))))
      (.block (last regs)))

/-- Counter block `i` into `b`: the counter block with its last word replaced
by the counter plus `i`, big-endian. -/
def ctr1 (b : VReg) (i : Nat) : List Instr :=
  [.addImm .w .x12 .x10 i, .rev32 .x12 .x12, .ldrq b .x2 0, .vop (.ins .s4 b 3 .x12)]

/-- Counter blocks `i`, `i + 1`, … into the registers. -/
def ctrs : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, i => ctr1 b i ++ ctrs bs (i + 1)

/-- XOR block register `b` into the data block `x3 + 16 j`. -/
def xor1 (b : VReg) (j : Nat) : List Instr :=
  [.ldrq .v31 .x3 (16 * j), .vop (.logic .eor b b .v31), .strq b .x3 (16 * j)]

/-- XOR the registers into the data blocks `j`, `j + 1`, …. -/
def xorData : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => xor1 b j ++ xorData bs (j + 1)

def regs8 : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7]

/-- Eight blocks; `x13 = n / 8` for the blocks left. -/
def body8 : Prog isa :=
  .seq (.block (ctrs regs8 0))
    (.seq (aes regs8)
      (.block (xorData regs8 0 ++ [.addImm .w .x10 .x10 8, .addImm .x .x3 .x3 128,
        .subImm .x .x4 .x4 8, .lsr .x .x13 .x4 3])))

/-- One block. -/
def body1 : Prog isa :=
  .seq (.block (ctrs [.v0] 0))
    (.seq (aes [.v0])
      (.block (xorData [.v0] 0 ++ [.addImm .w .x10 .x10 1, .addImm .x .x3 .x3 16,
        .subImm .x .x4 .x4 1])))

/-- Load the round keys, and set up `x6`, `x7`, the counter `w10` and `x13 = n / 8`. -/
def setup : List Instr :=
  (List.range 13).map (fun j => .ldrq (kreg j) .x0 (16 * j)) ++
  [.lsl .x .x9 .x1 4, .add .x .x9 .x0 .x9, .ldrq .v30 .x9 0, .subImm .x .x9 .x9 16,
   .ldrq .v29 .x9 0, .subImm .x .x6 .x1 10, .subImm .x .x7 .x1 12,
   .ldr .w .x10 .x2 12, .rev32 .x10 .x10, .lsr .x .x13 .x4 3]

/-- Write the final counter back. -/
def ctrStore : List Instr := [.rev32 .x12 .x10, .str .w .x12 .x2 12]

def ctr32 : Prog isa :=
  .seq (.block setup)
    (.seq (.ite (.zero .x .x13) (.block []) (.loop body8 (.nonzero .x .x13)))
      (.seq (.ite (.zero .x .x4) (.block []) (.loop body1 (.nonzero .x .x4)))
        (.block ctrStore)))

end VG.Impl.Aes.AArch64.Aese
