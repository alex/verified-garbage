import VerifiedGarbage.Impl.CmacTripleDes.Index
import VerifiedGarbage.TCB.Arm.Isa

/-!
# DES on 32-bit ARM, in constant time: the round, the block and the key schedule

Untrusted: the proofs check everything here.

As on 64-bit targets (`Impl/CmacTripleDes/X86_64/Round.lean`), bit
permutations are XORs of rotated and masked *groups* of a source word
(`groups`, `linCode`), and the S-boxes a multiplexer tree over constant
leaves (`mux`). With 32-bit words the 48 bits of `E(R) ⊕ K` are formed as
two halves of 24 bits: half 0 holds boxes 4–7 (box `i` in bits
`6 (7 - i) …`), half 1 boxes 0–3 (box `i` in bits `6 (3 - i) …`). Each half
is broadcast to six slots and evaluated by its own tree, and `P` gathers the
output bits from both.

The registers: `L` in `r7`, `R` in `r8`, the round key at `[r9]` (its low
word, then its high word), the scratch buffer at `r10` (the broadcast inputs
in slots 0–11, half 0's outputs in slot 12), the round counter in `r11`, the
pass counter in `r12` and the step from one round key to the next (8 or −8)
in `lr`. A round uses `r0`–`r6`.
-/

namespace VG.Impl.CmacTripleDes.Arm

open VG.Arm VG.Impl.CmacTripleDes

/-- `mov d, n`. -/
def mov (d n : Reg) : Instr := .mov d (.reg n)

/-- The constant `v` into `d`: `movw` of its low half, and `movt` of its
high half if it is not zero. -/
def movImm (d : Reg) (v : Nat) : List Instr :=
  .movw d (BitVec.ofNat 16 v) :: (if v / 65536 % 65536 = 0 then [] else [.movt d (BitVec.ofNat 16 (v / 65536))])

/-! ## Bit permutations -/

/-- The groups of a bit map on 32-bit words: for each rotation `r` (right)
that some destination bit `d < n` needs (its source `src d` is bit
`(d + r) % 32`), the mask of those destination bits. -/
def groups (src : Nat → Option Nat) (n : Nat) : List (Nat × Nat) :=
  -- Every rotation's mask at once, in one pass over the bits (the kernel
  -- evaluates this): rotation `r`'s in bits `[n r, n r + n)` of `ms`.
  let ms := (List.range n).foldl (fun ms d =>
    match src d with
    | some s => ms ||| (2 ^ d) <<< (n * ((s + 32 - d) % 32))
    | none => ms) 0
  (List.range 32).filterMap fun r =>
    let m := (ms >>> (n * r)) % 2 ^ n
    if m = 0 then none else some (r, m)

/-- `src` rotated right by `r`. -/
def rot (src : Reg) (r : Nat) : Op2 := if r = 0 then .reg src else .shifted src .ror r

/-- One group: `src` rotated right by `r`, masked by `m` (in `u`), into `t`. -/
def group (src t u : Reg) (r m : Nat) : List Instr := movImm u m ++ [.dp .and t u (rot src r)]

/-- The XOR of the groups `gs` of `src` into `dst` (`t` and `u` are
clobbered); `dst` is first set to the first group if `init`. -/
def linCode (src dst t u : Reg) (init : Bool) : List (Nat × Nat) → List Instr
  | [] => []
  | (r, m) :: gs =>
    if init then group src dst u r m ++ linCode src dst t u false gs
    else group src t u r m ++ [.dp .eor dst dst (.reg t)] ++ linCode src dst t u false gs

/-! ## The round -/

/-- The position, within its lane, of output bit `b` of box `i`. -/
def off (i b : Nat) : Nat :=
  ([[1, 2, 3, 0], [0, 1, 3, 2], [3, 2, 1, 0], [2, 0, 3, 1], [3, 0, 2, 1], [3, 1, 2, 0],
    [3, 0, 2, 1], [3, 1, 0, 2]].getD i []).getD b 0

/-- Bit `q` of half `h` of `E(R)` is bit `expSrc (24 h + q)` of `R`. -/
def eSrc (h q : Nat) : Option Nat := if q < 24 then some (expSrc (24 * h + q)) else none

/-- Bits `6 j`, `j < 4`. -/
def lanes6 : Nat := 1 + 2 ^ 6 + 2 ^ 12 + 2 ^ 18

/-- The broadcast inputs: slot `6 h + k` holds, at bits `6 j + o` for `o < 4`,
bit `k` of lane `j` of half `h` of `E(R) ⊕ K`. Half 0 is formed in `r0`,
half 1 in `r1`. -/
def inputs : List Instr :=
  linCode .r8 .r0 .r2 .r6 true (groups (eSrc 0) 24) ++
  linCode .r8 .r1 .r3 .r6 true (groups (eSrc 1) 24) ++
  [.ldr .r2 .r9 0, .dp .eor .r0 .r0 (.reg .r2), .dp .eor .r1 .r1 (.shifted .r2 .lsr 24),
   .ldr .r2 .r9 4] ++ movImm .r6 65535 ++
  [.dp .and .r2 .r6 (.reg .r2), .dp .eor .r1 .r1 (.shifted .r2 .ror 24)] ++ movImm .r6 lanes6 ++
  ([Reg.r0, .r1].zipIdx.flatMap fun (v, h) => (List.range 6).flatMap fun k =>
    [.dp .and .r2 .r6 (if k = 0 then .reg v else .shifted v .lsr k),
     .dp .eor .r2 .r2 (.shifted .r2 .ror 31), .dp .eor .r2 .r2 (.shifted .r2 .ror 30),
     .str .r2 .r10 (4 * (6 * h + k))])

/-- The box in lane `j` of half `h`. -/
def boxOf (h j : Nat) : Nat := 7 - 4 * h - j

/-- The leaf constant of half `h` for the input `e`: at bit `6 j + off i b`
(`i` the box in lane `j`), output bit `b` of box `i` on `e`. -/
def leaf (h e : Nat) : Nat :=
  (List.range 4).foldl (fun c j =>
    let i := boxOf h j
    let v := Spec.TripleDes.sBox i (BitVec.ofNat 6 e)
    (List.range 4).foldl (fun c b =>
      if v.getLsbD b then c ||| 2 ^ (6 * j + off i b) else c) c) 0

/-- The registers of the multiplexer tree: level `l`'s second operand is
in `muxReg l`. -/
def muxReg : Nat → Reg
  | 0 => .r0 | 1 => .r1 | 2 => .r2 | 3 => .r3 | 4 => .r4 | _ => .r5

/-- Node `j` of level `l` of half `h`'s tree (the leaves `2 ^ l j … 2 ^ l (j + 1) - 1`,
told apart by inputs `0 … l - 1`, in slots `6 h …`) into `dst`; `r6` holds
the leaf constants and the inputs. -/
def mux (h : Nat) : Nat → Nat → Reg → List Instr
  | 0, _, _ => []
  | 1, j, dst =>
    movImm dst (leaf h (2 * j) ^^^ leaf h (2 * j + 1)) ++
      [.ldr .r6 .r10 (4 * (6 * h)), .dp .and dst dst (.reg .r6)] ++ movImm .r6 (leaf h (2 * j)) ++
      [.dp .eor dst dst (.reg .r6)]
  | l + 1, j, dst =>
    mux h l (2 * j) dst ++ mux h l (2 * j + 1) (muxReg l) ++
      [.dp .eor (muxReg l) (muxReg l) (.reg dst), .ldr .r6 .r10 (4 * (6 * h + l)),
       .dp .and (muxReg l) (muxReg l) (.reg .r6), .dp .eor dst dst (.reg (muxReg l))]

/-- The S-boxes: half 0's outputs to slot 12, half 1's in `r0`. -/
def sboxes : List Instr := mux 0 6 0 .r0 ++ [.str .r0 .r10 48] ++ mux 1 6 0 .r0

/-- Bit `u` of the S-boxes' outputs is bit `outPos u` of half `outHalf u`. -/
def outHalf (u : Nat) : Nat := if u / 4 < 4 then 0 else 1
def outPos (u : Nat) : Nat := 6 * (u / 4 % 4) + off (7 - u / 4) (u % 4)

/-- `L ⊕ P(S)` into `r7` (half 0's outputs loaded into `r1`), and `L` and `R`
exchanged. -/
def output : List Instr :=
  [.ldr .r1 .r10 48] ++
  linCode .r1 .r7 .r2 .r6 false
    (groups (fun j => if j < 32 ∧ outHalf (pSrc j) = 0 then some (outPos (pSrc j)) else none) 32) ++
  linCode .r0 .r7 .r2 .r6 false
    (groups (fun j => if j < 32 ∧ outHalf (pSrc j) = 1 then some (outPos (pSrc j)) else none) 32) ++
  [mov .r0 .r8, mov .r8 .r7, mov .r7 .r0]

/-- One round: `(L, R) := (R, L ⊕ f(R, K))`. -/
def round : List Instr := inputs ++ sboxes ++ output

/-! ## The block -/

/-- The next round key, and the round counter decremented (Z set at 0). -/
def roundTail : List Instr := [.dp .add .r9 .r9 (.reg .lr), .subs .r11 .r11 (.imm 1)]

/-- Sixteen rounds, with the round keys from `[r9]` on, `lr` bytes apart. -/
def pass : Prog isa :=
  .seq (.block [.mov .r11 (.imm 16)]) (.loop (.block (round ++ roundTail)) .ne)

/-- Between passes: `r9` to the next pass's first round key (`128 − lr`
on), the step negated, `L` and `R` exchanged, and the pass counter
decremented (Z set at 0). -/
def passTail : List Instr :=
  [.mov .r0 (.imm 128), .dp .sub .r0 .r0 (.reg .lr), .dp .add .r9 .r9 (.reg .r0),
   .mov .r0 (.imm 0), .dp .sub .lr .r0 (.reg .lr),
   mov .r0 .r7, mov .r7 .r8, mov .r8 .r0,
   .subs .r12 .r12 (.imm 1)]

/-- `IP` of the block in `r0` (its high word) and `r1` (its low word): its
high half into `r7` (`L`), its low half into `r8` (`R`). -/
def ipCode : List Instr :=
  linCode .r0 .r7 .r2 .r6 true
    (groups (fun t => if t < 32 ∧ 32 ≤ ipSrc (32 + t) then some (ipSrc (32 + t) - 32) else none) 32) ++
  linCode .r1 .r7 .r2 .r6 false
    (groups (fun t => if t < 32 ∧ ipSrc (32 + t) < 32 then some (ipSrc (32 + t)) else none) 32) ++
  linCode .r0 .r8 .r2 .r6 true
    (groups (fun t => if t < 32 ∧ 32 ≤ ipSrc t then some (ipSrc t - 32) else none) 32) ++
  linCode .r1 .r8 .r2 .r6 false
    (groups (fun t => if t < 32 ∧ ipSrc t < 32 then some (ipSrc t) else none) 32)

/-- `IP⁻¹(R ‖ L)` into `r0` (high word) and `r1` (low word), with `R` in
`r7` and `L` in `r8` (after the last pass's exchange). -/
def fpCode : List Instr :=
  linCode .r7 .r0 .r2 .r6 true
    (groups (fun t => if t < 32 ∧ 32 ≤ fpSrc (32 + t) then some (fpSrc (32 + t) - 32) else none) 32) ++
  linCode .r8 .r0 .r2 .r6 false
    (groups (fun t => if t < 32 ∧ fpSrc (32 + t) < 32 then some (fpSrc (32 + t)) else none) 32) ++
  linCode .r7 .r1 .r2 .r6 true
    (groups (fun t => if t < 32 ∧ 32 ≤ fpSrc t then some (fpSrc t - 32) else none) 32) ++
  linCode .r8 .r1 .r2 .r6 false
    (groups (fun t => if t < 32 ∧ fpSrc t < 32 then some (fpSrc t) else none) 32)

/-- TDEA encryption (`E_K3(D_K2(E_K1(x)))`) of the block `x` in `r0:r1`
(its high and low words), into `r0:r1`, with the key schedule at `r9`: the
passes share one `IP` and one `IP⁻¹`, which cancel between them. `r9` is
restored. -/
def block : Prog isa :=
  .seq (.block (ipCode ++ [.mov .r12 (.imm 3), .mov .lr (.imm 8)]))
    (.seq (.loop (.seq pass (.block passTail)) .ne)
      (.block ([.dp .sub .r9 .r9 (.imm 504)] ++ fpCode)))

/-! ## The key schedule -/

/-- The sixteen round keys of the DES key in `r0:r1` (its high and low
words), to `[r2 + 8 j]` (the low word) and `[r2 + 8 j + 4]` (the high
word). -/
def roundKeys : List Instr :=
  (List.range 16).flatMap fun j =>
    let w (lo : Nat) (hi : Bool) : Nat → Option Nat := fun q =>
      if q < (if lo = 0 then 32 else 16) ∧ (32 ≤ rkSrc j (lo + q)) = hi then
        some (if hi then rkSrc j (lo + q) - 32 else rkSrc j (lo + q)) else none
    linCode .r0 .r6 .r7 .r8 true (groups (w 0 true) 32) ++ linCode .r1 .r6 .r7 .r8 false (groups (w 0 false) 32) ++
      [.str .r6 .r2 (8 * j)] ++
    linCode .r0 .r6 .r7 .r8 true (groups (w 32 true) 32) ++ linCode .r1 .r6 .r7 .r8 false (groups (w 32 false) 32) ++
      [.str .r6 .r2 (8 * j + 4)]

end VG.Impl.CmacTripleDes.Arm
