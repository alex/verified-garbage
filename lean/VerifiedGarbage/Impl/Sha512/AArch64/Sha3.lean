import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-512 compression with FEAT_SHA512 (Rust's `sha3` feature)

State pairs AB/CD/EF/GH occupy v0–v3; v16–v23 hold the sixteen-word
schedule window. v24–v27 retain the input state for feed-forward. All
registers are caller-saved, and scratch is unused.
-/

namespace VG.Impl.Sha512.AArch64.Sha3

open VG.AArch64
open VG.Spec.Sha512 (K)

def msg (i : Nat) : VReg :=
  [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23].getD (i % 8) .v16

def constant (i j : Nat) : List Instr :=
  [.movz .x .x4 ((K (2 * i + j)).extractLsb' 0 16) 0,
   .movk .x .x4 ((K (2 * i + j)).extractLsb' 16 16) 1,
   .movk .x .x4 ((K (2 * i + j)).extractLsb' 32 16) 2,
   .movk .x .x4 ((K (2 * i + j)).extractLsb' 48 16) 3,
   -- A full write for the first lane breaks the dependency on the previous
   -- round's v4. Inserting both lanes would keep that SHA512H2 result live.
   .vop (if j = 0 then .dup .d2 .v4 .x4 else .ins .d2 .v4 j .x4)]

def schedule (i : Nat) : List Instr :=
  if i < 8 then
    [.ldrq (msg i) .x1 (16 * i), .vop (.rev .rev64b (msg i) (msg i))]
  else
    [.vop (.ext .v6 (msg (i + 4)) (msg (i + 5)) 8),
     .vop (.sha512su0 (msg i) (msg (i + 1))),
     .vop (.sha512su1 (msg i) (msg (i + 7)) .v6)]

def rounds2 (i : Nat) : List Instr :=
  constant i 0 ++ constant i 1 ++
  [.vop (.add .d2 .v4 .v4 (msg i)),
   .vop (.ext .v4 .v4 .v4 8),
   .vop (.add .d2 .v4 .v4 .v3),
   .vop (.ext .v5 .v2 .v3 8),
   .vop (.ext .v6 .v1 .v2 8),
   .vop (.sha512h .v4 .v5 .v6),
   .vop (.add .d2 .v5 .v1 .v4),
   .vop (.sha512h2 .v4 .v1 .v0),
   .vop (.mov .v3 .v2), .vop (.mov .v1 .v0),
   .vop (.mov .v0 .v4), .vop (.mov .v2 .v5)]

def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ rounds2 n))

def load : List Instr :=
  [.ldrq .v0 .x0 0, .ldrq .v1 .x0 16, .ldrq .v2 .x0 32, .ldrq .v3 .x0 48,
   .vop (.mov .v24 .v0), .vop (.mov .v25 .v1),
   .vop (.mov .v26 .v2), .vop (.mov .v27 .v3)]

def store : List Instr :=
  [.vop (.add .d2 .v0 .v0 .v24), .vop (.add .d2 .v1 .v1 .v25),
   .vop (.add .d2 .v2 .v2 .v26), .vop (.add .d2 .v3 .v3 .v27),
   .strq .v0 .x0 0, .strq .v1 .x0 16, .strq .v2 .x0 32, .strq .v3 .x0 48,
   .addImm .x .x1 .x1 128, .subImm .x .x2 .x2 1]

def body : Prog isa := .seq (.block load) (.seq (rounds 40) (.block store))
def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.loop body (.nonzero .x .x2))

end VG.Impl.Sha512.AArch64.Sha3
