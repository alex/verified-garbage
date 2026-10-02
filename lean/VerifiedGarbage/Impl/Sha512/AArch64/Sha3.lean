import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-512 compression with FEAT_SHA512 (Rust's `sha3` feature)

The state pairs AB/CD/EF/GH and the two results of each pair of rounds
occupy v0–v5, renamed rather than moved from one pair of rounds to the next
(`reg`); v16–v23 hold the sixteen-word schedule window. v24–v27 hold the
hash value across the blocks (loaded once, updated and stored after each
block), and v31 is zero throughout. All registers are caller-saved, and
scratch is unused.

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

/-- The register of state pair AB, CD, EF or GH (`k = 0 … 3`) in pair of
rounds `i`, and of its two results (`k = 4, 5`): the next AB and EF. Each
pair of rounds renames them, with period 3. -/
def reg (i k : Nat) : VReg :=
  ([[.v0, .v1, .v2, .v3, .v4, .v5], [.v4, .v0, .v5, .v2, .v1, .v3],
    [.v1, .v4, .v3, .v5, .v0, .v2]].getD (i % 3) []).getD k .v0

/-- `Kᵢ` pairs into `d`. -/
def constant (i j : Nat) (d : VReg) : List Instr :=
  [.movz .x .x4 ((K (2 * i + j)).extractLsb' 0 16) 0,
   .movk .x .x4 ((K (2 * i + j)).extractLsb' 16 16) 1,
   .movk .x .x4 ((K (2 * i + j)).extractLsb' 32 16) 2,
   .movk .x .x4 ((K (2 * i + j)).extractLsb' 48 16) 3,
   -- A full write for the first lane breaks the dependency on the register's
   -- previous value. Inserting both lanes would keep it live.
   .vop (if j = 0 then .dup .d2 d .x4 else .ins .d2 d j .x4)]

def schedule (i : Nat) : List Instr :=
  if i < 8 then
    [.ldrq (msg i) .x1 (16 * i), .vop (.rev .rev64b (msg i) (msg i))]
  else
    [.vop (.ext .v6 (msg (i + 4)) (msg (i + 5)) 8),
     .vop (.sha512su0 (msg i) (msg (i + 1))),
     .vop (.sha512su1 (msg i) (msg (i + 7)) .v6)]

/-- Pair of rounds `i` with the state pairs in `ab`, `cd`, `ef`, `gh`, leaving
the next AB in `t` and the next EF in `f`. -/
def rounds2With (i : Nat) (ab cd ef gh t f : VReg) : List Instr :=
  constant i 0 t ++ constant i 1 t ++
  [.vop (.add .d2 t t (msg i)),
   .vop (.ext t t t 8),
   -- t = GH + K + W, the accumulator of the usual SHA512H; f = t + CD.
   .vop (.add .d2 t t gh),
   .vop (.add .d2 f t cd),
   .vop (.ext .v6 ef gh 8),
   .vop (.ext .v7 .v31 ef 8),
   .vop (.ext .v28 cd ef 8),
   -- f := the next EF, from (0, e); t := the usual sums, from (d, e); then
   -- t := the next AB.
   .vop (.sha512h f .v6 .v7),
   .vop (.sha512h t .v6 .v28),
   .vop (.sha512h2 t cd ab)]

def rounds2 (i : Nat) : List Instr :=
  rounds2With i (reg i 0) (reg i 1) (reg i 2) (reg i 3) (reg i 4) (reg i 5)

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

/-- After the 40 pairs of rounds the state is in `reg 40 0 … reg 40 3`. -/
def store : List Instr :=
  [.vop (.add .d2 .v24 (reg 40 0) .v24), .vop (.add .d2 .v25 (reg 40 1) .v25),
   .vop (.add .d2 .v26 (reg 40 2) .v26), .vop (.add .d2 .v27 (reg 40 3) .v27),
   .strq .v24 .x0 0, .strq .v25 .x0 16, .strq .v26 .x0 32, .strq .v27 .x0 48,
   .addImm .x .x1 .x1 128, .subImm .x .x2 .x2 1]

def body : Prog isa := .seq (.block load) (.seq (rounds 40) (.block store))
def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block init) (.loop body (.nonzero .x .x2)))

end VG.Impl.Sha512.AArch64.Sha3
