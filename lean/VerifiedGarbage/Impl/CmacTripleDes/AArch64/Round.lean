import VerifiedGarbage.Impl.CmacTripleDes.Index
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# DES on AArch64, in constant time: the round, the block and the key schedule

As on x86-64 (`Impl/CmacTripleDes/X86_64/Round.lean`), whose structure this
follows register for register: bit permutations are XORs of rotated and
masked *groups* of the source (`groups`, `linCode`), and the eight S-boxes
are a multiplexer tree over constant leaves (`mux`) on all eight boxes'
inputs at once, broadcast to four bit positions each. Constants are built
with `movz` and `movk` (`movImm`), and the model's loads have no register
operands, so a slot is loaded before it is used.

The registers: `L` in `x12` and `R` in `x13` (the low 32 bits; the high bits
are ignored), the round key at `[x14]`, the scratch buffer at `x15` (the
broadcast inputs in slots 0–5), the round counter in `x16`, the pass counter
in `x17` and the step from one round key to the next (8 or −8) in `x0`. A
round uses `x5`–`x11`. Only `x0`–`x17` are used: nothing the caller keeps.
-/

namespace VG.Impl.CmacTripleDes.AArch64

open VG.AArch64 VG.Impl.CmacTripleDes

/-- `mov d, n`. -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The constant `v` into `d`: `movz` of its low halfword, and `movk` of
each other nonzero one. -/
def movImm (d : Reg) (v : Nat) : List Instr :=
  .movz .x d (BitVec.ofNat 16 v) 0 ::
    ((List.range 3).filterMap fun h =>
      if (v >>> (16 * (h + 1))) % 65536 = 0 then none
      else some (.movk .x d (BitVec.ofNat 16 (v >>> (16 * (h + 1)))) (h + 1)))

/-! ## Bit permutations -/

/-- The groups of a bit map: for each rotation `r` (right) that some
destination bit `d < n` needs (its source `src d` is bit `(d + r) % 64`),
the mask of those destination bits. -/
def groups (src : Nat → Option Nat) (n : Nat) : List (Nat × Nat) :=
  -- Every rotation's mask at once, in one pass over the bits (the kernel
  -- evaluates this): rotation `r`'s in bits `[n r, n r + n)` of `ms`.
  let ms := (List.range n).foldl (fun ms d =>
    match src d with
    | some s => ms ||| (2 ^ d) <<< (n * ((s + 64 - d) % 64))
    | none => ms) 0
  (List.range 64).filterMap fun r =>
    let m := (ms >>> (n * r)) % 2 ^ n
    if m = 0 then none else some (r, m)

/-- One group: `src` rotated right by `r`, masked by `m` (in `u`), into `t`. -/
def group (src t u : Reg) (r m : Nat) : List Instr :=
  movImm u m ++
    (if r = 0 then [.logic .and .x t src u] else [.ror .x t src r, .logic .and .x t t u])

/-- The XOR of the groups `gs` of `src` into `dst` (`t` and `u` are
clobbered); `dst` is first set to the first group if `init`. -/
def linCode (src dst t u : Reg) (init : Bool) : List (Nat × Nat) → List Instr
  | [] => []
  | (r, m) :: gs =>
    if init then group src dst u r m ++ linCode src dst t u false gs
    else group src t u r m ++ [.logic .eor .x dst dst t] ++ linCode src dst t u false gs

/-! ## The round -/

/-- The position, within its lane, of output bit `b` of box `i`. -/
def off (i b : Nat) : Nat :=
  ([[1, 2, 3, 0], [0, 1, 3, 2], [3, 2, 1, 0], [2, 0, 3, 1], [3, 0, 2, 1], [3, 1, 2, 0],
    [3, 0, 2, 1], [3, 1, 0, 2]].getD i []).getD b 0

/-- Bit `6 (7 - i) + k` of a word of 64 bits holding `R` in both halves is
the expansion's bit `6 (7 - i) + k`, `15 - 2 i` places below it. -/
def eSrc (p : Nat) : Option Nat :=
  if p < 48 then some ((27 + 64 - 4 * (7 - p / 6) + p % 6) % 64) else none

/-- Bits `6 j`, `j < 8`. -/
def lanes6 : Nat := (List.range 8).foldl (fun m j => m ||| 2 ^ (6 * j)) 0

/-- The broadcast inputs: slot `k` holds, at bits `6 (7 - i) + o` for
`o < 4`, bit `k` of box `i`'s input `E(R) ⊕ K`. `R` (masked to 32 bits) is
doubled into `x5`, `E(R) ⊕ K` formed in `x6`. -/
def inputs : List Instr :=
  movImm .x11 (2 ^ 32 - 1) ++
  [.logic .and .x .x5 .x13 .x11, .ror .x .x6 .x5 32, .logic .eor .x .x5 .x5 .x6] ++
  linCode .x5 .x6 .x7 .x11 true (groups eSrc 48) ++
  [.ldr .x .x7 .x14 0, .logic .eor .x .x6 .x6 .x7] ++ movImm .x5 lanes6 ++
  (List.range 6).flatMap fun k =>
    (if k = 0 then [.logic .and .x .x7 .x6 .x5] else [.lsr .x .x7 .x6 k, .logic .and .x .x7 .x7 .x5]) ++
    [.ror .x .x11 .x7 63, .logic .eor .x .x7 .x7 .x11, .ror .x .x11 .x7 62,
     .logic .eor .x .x7 .x7 .x11, .str .x .x7 .x15 (8 * k)]

/-- The leaf constant for the input `e`: at bit `6 (7 - i) + off i b`,
output bit `b` of box `i` on `e`. -/
def leaf (e : Nat) : Nat :=
  (List.range 8).foldl (fun c i =>
    let v := Spec.TripleDes.sBox i (BitVec.ofNat 6 e)
    (List.range 4).foldl (fun c b =>
      if v.getLsbD b then c ||| 2 ^ (6 * (7 - i) + off i b) else c) c) 0

/-- The registers of the multiplexer tree: level `l`'s second operand is
in `muxReg l`. -/
def muxReg : Nat → Reg
  | 0 => .x5 | 1 => .x6 | 2 => .x7 | 3 => .x8 | 4 => .x9 | _ => .x10

/-- Node `j` of level `l` of the tree (the leaves `2 ^ l j … 2 ^ l (j + 1) - 1`,
told apart by inputs `0 … l - 1`) into `dst`; `x11` holds the leaf
constants and the inputs. -/
def mux : Nat → Nat → Reg → List Instr
  | 0, _, _ => []
  | 1, j, dst =>
    movImm dst (leaf (2 * j) ^^^ leaf (2 * j + 1)) ++
      [.ldr .x .x11 .x15 0, .logic .and .x dst dst .x11] ++ movImm .x11 (leaf (2 * j)) ++
      [.logic .eor .x dst dst .x11]
  | l + 1, j, dst =>
    mux l (2 * j) dst ++ mux l (2 * j + 1) (muxReg l) ++
      [.logic .eor .x (muxReg l) (muxReg l) dst, .ldr .x .x11 .x15 (8 * l),
       .logic .and .x (muxReg l) (muxReg l) .x11, .logic .eor .x dst dst (muxReg l)]

/-- The S-boxes, into `x5`. -/
def sboxes : List Instr := mux 6 0 .x5

/-- Bit `u` of the S-boxes' outputs is at `outPos u` in `x5`. -/
def outPos (u : Nat) : Nat := 6 * (u / 4) + off (7 - u / 4) (u % 4)

/-- `L ⊕ P(S)` into `x12`, and `L` and `R` exchanged. -/
def output : List Instr :=
  linCode .x5 .x12 .x6 .x11 false (groups (fun j => if j < 32 then some (outPos (pSrc j)) else none) 32) ++
  [mov .x5 .x13, mov .x13 .x12, mov .x12 .x5]

/-- One round: `(L, R) := (R, L ⊕ f(R, K))`. -/
def round : List Instr := inputs ++ sboxes ++ output

/-! ## The block -/

/-- The next round key, and the round counter decremented. -/
def roundTail : List Instr := [.add .x .x14 .x14 .x0, .subImm .x .x16 .x16 1]

/-- Sixteen rounds, with the round keys from `[x14]` on, `x0` bytes apart. -/
def pass : Prog isa :=
  .seq (.block [.movz .x .x16 16 0]) (.loop (.block (round ++ roundTail)) (.nonzero .x .x16))

/-- Between passes: `x14` to the next pass's first round key (`128 − x0`
on), the step negated, `L` and `R` exchanged, and the pass counter
decremented. -/
def passTail : List Instr :=
  [.movz .x .x5 128 0, .sub .x .x5 .x5 .x0, .add .x .x14 .x14 .x5,
   .movz .x .x5 0 0, .sub .x .x0 .x5 .x0,
   mov .x5 .x12, mov .x12 .x13, mov .x13 .x5,
   .subImm .x .x17 .x17 1]

/-- `IP` of the block in `x5`: its high half into `x12` (`L`), its low half
into `x13` (`R`). -/
def ipCode : List Instr :=
  linCode .x5 .x12 .x6 .x11 true (groups (fun t => if t < 32 then some (ipSrc (32 + t)) else none) 32) ++
  linCode .x5 .x13 .x6 .x11 true (groups (fun t => if t < 32 then some (ipSrc t) else none) 32)

/-- `IP⁻¹(R ‖ L)` into `x5`, with `R` in `x12` and `L` in `x13` (after the
last pass's exchange). -/
def fpCode : List Instr :=
  linCode .x12 .x5 .x6 .x11 true
    (groups (fun j => if j < 64 ∧ 32 ≤ fpSrc j then some (fpSrc j - 32) else none) 64) ++
  linCode .x13 .x5 .x6 .x11 false
    (groups (fun j => if j < 64 ∧ fpSrc j < 32 then some (fpSrc j) else none) 64)

/-- TDEA encryption (`E_K3(D_K2(E_K1(x)))`) of the block `x` in `x5` (as a
64-bit integer), into `x5`, with the key schedule at `x14`: the passes share
one `IP` and one `IP⁻¹`, which cancel between them. `x14` is restored. -/
def block : Prog isa :=
  .seq (.block (ipCode ++ [.movz .x .x17 3 0, .movz .x .x0 8 0]))
    (.seq (.loop (.seq pass (.block passTail)) (.nonzero .x .x17))
      (.block ([.subImm .x .x14 .x14 504] ++ fpCode)))

/-! ## The key schedule -/

/-- The sixteen round keys of the DES key in `x5` (as a 64-bit integer), to
`[x2 + 8 j]`. -/
def roundKeys : List Instr :=
  (List.range 16).flatMap fun j =>
    linCode .x5 .x6 .x7 .x11 true (groups (fun q => if q < 48 then some (rkSrc j q) else none) 48) ++
      [.str .x .x6 .x2 (8 * j)]

end VG.Impl.CmacTripleDes.AArch64
