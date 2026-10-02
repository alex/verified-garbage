import VerifiedGarbage.Impl.Aes.AArch64.Aese

/-! AES-CMAC chaining with FEAT_AES. Round keys are loaded once, and the
chaining value remains in v0 for the entire update. No scratch or stack is
used, and no callee-saved register is written. -/
namespace VG.Impl.CmacAes.AArch64.Aese
open VG.AArch64
open VG.Impl.Aes.AArch64.Aese (kreg rnd)

def setupKeys : List Instr :=
  (List.range 13).map (fun j => .ldrq (kreg j) .x0 (16 * j)) ++
  [.lsl .x .x9 .x1 4, .add .x .x9 .x0 .x9, .ldrq .v30 .x9 0,
   .subImm .x .x9 .x9 16, .ldrq .v29 .x9 0,
   .subImm .x .x6 .x1 10, .subImm .x .x7 .x1 12, .ldrq .v0 .x2 0]

/-- The first and last round keys are folded into each input block. The
chaining register holds C XOR the last round key between blocks. -/
def fold : List Instr :=
  [.vop (.logic .eor .v31 .v16 .v30), .vop (.logic .eor .v0 .v0 .v30)]

def setup : List Instr := setupKeys ++ fold

def absorb : List Instr :=
  [.ldrq .v1 .x3 0, .vop (.logic .eor .v1 .v1 .v31),
   .vop (.aese .v0 .v1), .vop (.aesmc .v0 .v0)]

/-- Rounds after the first, leaving the final AddRoundKey deferred until
return. The round count is selected once, outside the block loop. -/
def tail (middle : Nat) : Prog isa :=
  .seq (.block ((List.range middle).flatMap fun j => rnd [.v0] (kreg (j + 1))))
    (.block [.vop (.aese .v0 .v29)])

def advance : List Instr :=
  [.addImm .x .x3 .x3 16, .subImm .x .x4 .x4 1]

def body (middle : Nat) : Prog isa :=
  .seq (.block absorb) (.seq (tail middle) (.block advance))

def loops : Prog isa :=
  .ite (.zero .x .x6) (.loop (body 8) (.nonzero .x .x4))
    (.ite (.zero .x .x7) (.loop (body 10) (.nonzero .x .x4))
      (.loop (body 12) (.nonzero .x .x4)))

def update : Prog isa :=
  .ite (.zero .x .x4) (.block [])
    (.seq (.block setup)
      (.seq loops (.block [.vop (.logic .eor .v0 .v0 .v30), .strq .v0 .x2 0])))
end VG.Impl.CmacAes.AArch64.Aese
