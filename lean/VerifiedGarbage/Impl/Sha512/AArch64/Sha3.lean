import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-512 compression with FEAT_SHA512 (Rust's `sha3` feature)

State pairs AB/CD/EF/GH occupy v0–v3; v16–v23 hold the sixteen-word
schedule window. v24–v27 hold the hash value across the blocks (loaded once,
updated and stored after each block), and v31 is zero throughout. All
registers are caller-saved, and scratch is unused.

Each pair of rounds runs SHA512H twice. The usual sequence adds CD to
SHA512H's result to get the next EF, and extracts the next rounds' operands
from that sum: two vector operations between consecutive SHA512Hs. Here the
first SHA512H instead gets CD added to its accumulator, and a zero in place
of `d` in its third operand (`d` is added once, through the accumulator,
rather than inside the instruction), so it produces the next EF itself, and
the next rounds' operands are one EXT away from it. The second SHA512H
computes the usual sums for SHA512H2. On cores where SHA512H and SHA512H2
share one unpipelined unit (Apple M1: two cycles each, three to a vector
consumer, vector operations two), this trades seven cycles of latency per
pair of rounds for six of throughput.
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
   -- v4 = GH + K + W, the accumulator of the usual SHA512H; v5 = v4 + CD.
   .vop (.add .d2 .v4 .v4 .v3),
   .vop (.add .d2 .v5 .v4 .v1),
   .vop (.ext .v6 .v2 .v3 8),
   -- v5 := the next EF, from (0, e).
   .vop (.ext .v7 .v31 .v2 8),
   .vop (.sha512h .v5 .v6 .v7),
   -- v4 := the usual sums, from (d, e); v4 := the next AB.
   .vop (.ext .v7 .v1 .v2 8),
   .vop (.sha512h .v4 .v6 .v7),
   .vop (.sha512h2 .v4 .v1 .v0),
   .vop (.mov .v3 .v2), .vop (.mov .v1 .v0),
   .vop (.mov .v0 .v4), .vop (.mov .v2 .v5)]

def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ rounds2 n))

/-- Load the hash value into v24–v27 and zero v31, once. -/
def init : List Instr :=
  [.vop (.movi0 .v31),
   .ldrq .v24 .x0 0, .ldrq .v25 .x0 16, .ldrq .v26 .x0 32, .ldrq .v27 .x0 48]

def load : List Instr :=
  [.vop (.mov .v0 .v24), .vop (.mov .v1 .v25),
   .vop (.mov .v2 .v26), .vop (.mov .v3 .v27)]

def store : List Instr :=
  [.vop (.add .d2 .v24 .v0 .v24), .vop (.add .d2 .v25 .v1 .v25),
   .vop (.add .d2 .v26 .v2 .v26), .vop (.add .d2 .v27 .v3 .v27),
   .strq .v24 .x0 0, .strq .v25 .x0 16, .strq .v26 .x0 32, .strq .v27 .x0 48,
   .addImm .x .x1 .x1 128, .subImm .x .x2 .x2 1]

def body : Prog isa := .seq (.block load) (.seq (rounds 40) (.block store))
def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block init) (.loop body (.nonzero .x .x2)))

end VG.Impl.Sha512.AArch64.Sha3
