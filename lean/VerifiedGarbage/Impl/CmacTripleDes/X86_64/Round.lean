import VerifiedGarbage.Impl.CmacTripleDes.Index
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# DES on x86-64, in constant time: the round, the block and the key schedule

DES's permutations and S-boxes are computed without secret-dependent memory
accesses or branches, on 64-bit words:

* A bit permutation (IP, the expansion E, P, the round keys' selections)
  is a XOR of *groups*: the source rotated right by `r` and masked by the
  destination bits whose source bit is `r` places above them (`groups`,
  `linCode`).
* The eight S-boxes are evaluated at once by a multiplexer tree on 64-bit
  words (`mux`): box `i`'s six input bits are each broadcast to four bit
  positions of lane `7 - i` (bits `6 (7 - i) … 6 (7 - i) + 3`), one per
  output bit (`off`), and each leaf of the tree is a constant holding, at
  each of those positions, that output bit of that box for the leaf's
  input. Six levels of `x ⊕ ((x ⊕ y) ∧ sel)` pick the leaf of the input.

The registers: `L` in `r12` and `R` in `r13` (the low 32 bits; the high
bits are ignored), the round key at `[r14]`, the scratch buffer at `r15`
(the broadcast inputs in slots 0–5), the round counter in `r11`, the pass
counter in `r10` and the step from one round key to the next (8 or −8) in
`rbx`. A round uses `rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8` and `r9`.
-/

namespace VG.Impl.CmacTripleDes.X86_64

open VG.X86_64 VG.Impl.CmacTripleDes

/-! ## Bit permutations -/

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

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

/-- One group: `src` rotated right by `r`, masked by `m` (with `u`), into
`t`. -/
def group (src t u : Reg) (r m : Nat) : List Instr :=
  [.mov t (.reg src)] ++ (if r = 0 then [] else [.shift .ror t r]) ++
    [.movImm64 u (BitVec.ofNat 64 m), .alu .and t (.reg u)]

/-- The XOR of the groups `gs` of `src` into `dst` (`t` and `u` are
clobbered); `dst` is first set to the first group if `init`. -/
def linCode (src dst t u : Reg) (init : Bool) : List (Nat × Nat) → List Instr
  | [] => []
  | (r, m) :: gs =>
    if init then group src dst u r m ++ linCode src dst t u false gs
    else group src t u r m ++ [.alu .xor dst (.reg t)] ++ linCode src dst t u false gs

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
doubled into `rax`, `E(R) ⊕ K` formed in `rcx`. -/
def inputs : List Instr :=
  [.movImm64 .r9 (BitVec.ofNat 64 (2 ^ 32 - 1)), .mov .rax (.reg .r13), .alu .and .rax (.reg .r9),
   .mov .rcx (.reg .rax), .shift .ror .rcx 32, .alu .xor .rax (.reg .rcx)] ++
  linCode .rax .rcx .rdx .r9 true (groups eSrc 48) ++
  [.alu .xor .rcx (.mem (at_ .r14 0)), .movImm64 .rax (BitVec.ofNat 64 lanes6)] ++
  (List.range 6).flatMap fun k =>
    [.mov .rdx (.reg .rcx)] ++ (if k = 0 then [] else [.shift .shr .rdx k]) ++
    [.alu .and .rdx (.reg .rax), .mov .r9 (.reg .rdx), .shift .ror .r9 63, .alu .xor .rdx (.reg .r9),
     .mov .r9 (.reg .rdx), .shift .ror .r9 62, .alu .xor .rdx (.reg .r9),
     .store (at_ .r15 (8 * k)) .rdx]

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
  | 0 => .rax | 1 => .rcx | 2 => .rdx | 3 => .rsi | 4 => .rdi | _ => .r8

/-- Node `j` of level `l` of the tree (the leaves `2 ^ l j … 2 ^ l (j + 1) - 1`,
told apart by inputs `0 … l - 1`) into `dst`; `r9` holds the leaf
constants. -/
def mux : Nat → Nat → Reg → List Instr
  | 0, _, _ => []
  | 1, j, dst =>
    [.movImm64 dst (BitVec.ofNat 64 (leaf (2 * j) ^^^ leaf (2 * j + 1))),
     .alu .and dst (.mem (at_ .r15 0)), .movImm64 .r9 (BitVec.ofNat 64 (leaf (2 * j))),
     .alu .xor dst (.reg .r9)]
  | l + 1, j, dst =>
    mux l (2 * j) dst ++ mux l (2 * j + 1) (muxReg l) ++
      [.alu .xor (muxReg l) (.reg dst), .alu .and (muxReg l) (.mem (at_ .r15 (8 * l))),
       .alu .xor dst (.reg (muxReg l))]

/-- The S-boxes, into `rax`. -/
def sboxes : List Instr := mux 6 0 .rax

/-- Bit `u` of the S-boxes' outputs is at `outPos u` in `rax`. -/
def outPos (u : Nat) : Nat := 6 * (u / 4) + off (7 - u / 4) (u % 4)

/-- `L ⊕ P(S)` into `r12`, and `L` and `R` exchanged. -/
def output : List Instr :=
  linCode .rax .r12 .rcx .r9 false (groups (fun j => if j < 32 then some (outPos (pSrc j)) else none) 32) ++
  [.mov .rax (.reg .r13), .mov .r13 (.reg .r12), .mov .r12 (.reg .rax)]

/-- One round: `(L, R) := (R, L ⊕ f(R, K))`. -/
def round : List Instr := inputs ++ sboxes ++ output

/-! ## The block -/

/-- The next round key, and the round counter decremented. -/
def roundTail : List Instr := [.alu .add .r14 (.reg .rbx), .alu .sub .r11 (.imm 1)]

/-- Sixteen rounds, with the round keys from `[r14]` on, `rbx` bytes apart. -/
def pass : Prog isa :=
  .seq (.block [.mov32 .r11 (.imm 16)]) (.loop (.block (round ++ roundTail)) .ne)

/-- Between passes: `r14` to the next pass's first round key (`128 − rbx`
on), the step negated, `L` and `R` exchanged, and the pass counter
decremented. -/
def passTail : List Instr :=
  [.mov32 .rax (.imm 128), .alu .sub .rax (.reg .rbx), .alu .add .r14 (.reg .rax),
   .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbx), .mov .rbx (.reg .rax),
   .mov .rax (.reg .r12), .mov .r12 (.reg .r13), .mov .r13 (.reg .rax),
   .alu .sub .r10 (.imm 1)]

/-- `IP` of the block in `rax`: its high half into `r12` (`L`), its low half
into `r13` (`R`). -/
def ipCode : List Instr :=
  linCode .rax .r12 .rcx .r9 true (groups (fun t => if t < 32 then some (ipSrc (32 + t)) else none) 32) ++
  linCode .rax .r13 .rcx .r9 true (groups (fun t => if t < 32 then some (ipSrc t) else none) 32)

/-- `IP⁻¹(R ‖ L)` into `rax`, with `R` in `r12` and `L` in `r13` (after the
last pass's exchange). -/
def fpCode : List Instr :=
  linCode .r12 .rax .rcx .r9 true
    (groups (fun j => if j < 64 ∧ 32 ≤ fpSrc j then some (fpSrc j - 32) else none) 64) ++
  linCode .r13 .rax .rcx .r9 false
    (groups (fun j => if j < 64 ∧ fpSrc j < 32 then some (fpSrc j) else none) 64)

/-- TDEA encryption (`E_K3(D_K2(E_K1(x)))`) of the block `x` in `rax` (as a
64-bit integer), into `rax`, with the key schedule at `r14`: the passes
share one `IP` and one `IP⁻¹`, which cancel between them. `r14` is restored. -/
def block : Prog isa :=
  .seq (.block (ipCode ++ [.mov32 .r10 (.imm 3), .mov32 .rbx (.imm 8)]))
    (.seq (.loop (.seq pass (.block passTail)) .ne)
      (.block ([.alu .sub .r14 (.imm 504)] ++ fpCode)))

/-! ## The key schedule -/

/-- The sixteen round keys of the DES key in `rax` (as a 64-bit integer), to
`[rbp + 8 j]`. -/
def roundKeys : List Instr :=
  (List.range 16).flatMap fun j =>
    linCode .rax .rcx .rdx .r9 true (groups (fun q => if q < 48 then some (rkSrc j q) else none) 48) ++
      [.store (at_ .rbp (8 * j)) .rcx]

end VG.Impl.CmacTripleDes.X86_64
