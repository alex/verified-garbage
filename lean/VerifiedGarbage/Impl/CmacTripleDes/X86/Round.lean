import VerifiedGarbage.Impl.CmacTripleDes.Index
import VerifiedGarbage.TCB.X86.Isa

/-!
# DES on x86 (32-bit), in constant time: the round, the block and the key schedule

Untrusted: the proofs check everything here.

As on 32-bit ARM (`Impl/CmacTripleDes/Arm/Round.lean`): bit permutations
are XORs of rotated and masked *groups* of a source word (`groups`,
`linCode`), the S-boxes a multiplexer tree over constant leaves (`mux`), and
the 48 bits of `E(R) ⊕ K` two halves of 24 bits (half 0 holds boxes 4–7,
half 1 boxes 0–3), each broadcast to six slots and evaluated by its own
tree. With seven registers, the round's words live in slots of the scratch
buffer at `ebp`, and the round key at `[esi]` (its low word, then its high
word):

* slots 0–5 and 7–12: the broadcast inputs of halves 0 and 1 (half `h` in
  slots `7 h …`);
* slots 6 and 13: where each half's tree keeps its first subtree;
* slots 14 and 15: the halves' outputs;
* slots 16 and 17: `L` and `R`;
* slots 18–20: the round counter, the pass counter and the step from one
  round key to the next (8 or −8).
-/

namespace VG.Impl.CmacTripleDes.X86

open VG.X86 VG.Impl.CmacTripleDes

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- Slot `k` of the scratch buffer. -/
def slot (k : Nat) : Src := .mem (at_ .ebp (4 * k))

/-- The slots of `L` and `R`, and of the counters. -/
def slotL : Nat := 16
def slotR : Nat := 17
def slotRounds : Nat := 18
def slotPasses : Nat := 19
def slotStep : Nat := 20

/-! ## Bit permutations -/

/-- The groups of a bit map on 32-bit words: for each rotation `r` (right)
that some destination bit `d < n` needs (its source `src d` is bit
`(d + r) % 32`), the mask of those destination bits. -/
def groups (src : Nat → Option Nat) (n : Nat) : List (Nat × Nat) :=
  (List.range 32).filterMap fun r =>
    let m := (List.range n).foldl (fun m d =>
      match src d with
      | some s => if (s + 32 - d) % 32 = r then m ||| 2 ^ d else m
      | none => m) 0
    if m = 0 then none else some (r, m)

/-- One group: `src` rotated right by `r`, masked by `m`, into `t`. -/
def group (src : Src) (t : Reg) (r m : Nat) : List Instr :=
  .mov t src :: ((if r = 0 then [] else [.shift .ror t r]) ++ [.alu .and t (.imm (BitVec.ofNat 32 m))])

/-- The XOR of the groups `gs` of `src` into `dst` (`t` is clobbered);
`dst` is first set to the first group if `init`. -/
def linCode (src : Src) (dst t : Reg) (init : Bool) : List (Nat × Nat) → List Instr
  | [] => []
  | (r, m) :: gs =>
    if init then group src dst r m ++ linCode src dst t false gs
    else group src t r m ++ [.alu .xor dst (.reg t)] ++ linCode src dst t false gs

/-! ## The round -/

/-- The position, within its lane, of output bit `b` of box `i`. -/
def off (i b : Nat) : Nat :=
  ([[1, 2, 3, 0], [0, 1, 3, 2], [3, 2, 1, 0], [2, 0, 3, 1], [3, 0, 2, 1], [3, 1, 2, 0],
    [3, 0, 2, 1], [3, 1, 0, 2]].getD i []).getD b 0

/-- Bit `q` of half `h` of `E(R)` is bit `expSrc (24 h + q)` of `R`. -/
def eSrc (h q : Nat) : Option Nat := if q < 24 then some (expSrc (24 * h + q)) else none

/-- Bits `6 j`, `j < 4`. -/
def lanes6 : Nat := 1 + 2 ^ 6 + 2 ^ 12 + 2 ^ 18

/-- The broadcast inputs: slot `7 h + k` holds, at bits `6 j + o` for `o < 4`,
bit `k` of lane `j` of half `h` of `E(R) ⊕ K`. Half 0 is formed in `eax`,
half 1 in `ebx`. -/
def inputs : List Instr :=
  linCode (slot slotR) .eax .ecx true (groups (eSrc 0) 24) ++
  linCode (slot slotR) .ebx .ecx true (groups (eSrc 1) 24) ++
  [.alu .xor .eax (.mem (at_ .esi 0)), .mov .ecx (.mem (at_ .esi 0)), .shift .shr .ecx 24,
   .alu .xor .ebx (.reg .ecx), .mov .ecx (.mem (at_ .esi 4)), .alu .and .ecx (.imm 0xffff),
   .shift .ror .ecx 24, .alu .xor .ebx (.reg .ecx)] ++
  ([Reg.eax, .ebx].zipIdx.flatMap fun (v, h) => (List.range 6).flatMap fun k =>
    [.mov .ecx (.reg v)] ++ (if k = 0 then [] else [.shift .shr .ecx k]) ++
    [.alu .and .ecx (.imm (BitVec.ofNat 32 lanes6)),
     .mov .edx (.reg .ecx), .shift .ror .edx 31, .alu .xor .ecx (.reg .edx),
     .mov .edx (.reg .ecx), .shift .ror .edx 30, .alu .xor .ecx (.reg .edx),
     .store (at_ .ebp (4 * (7 * h + k))) .ecx])

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
  | 0 | 1 => .ebx | 2 => .ecx | 3 => .edx | _ => .edi

/-- Node `j` of level `l` of half `h`'s tree (the leaves `2 ^ l j … 2 ^ l (j + 1) - 1`,
told apart by inputs `0 … l - 1`, in slots `7 h …`) into `dst`. -/
def mux (h : Nat) : Nat → Nat → Reg → List Instr
  | 0, _, _ => []
  | 1, j, dst =>
    [.mov dst (slot (7 * h)), .alu .and dst (.imm (BitVec.ofNat 32 (leaf h (2 * j) ^^^ leaf h (2 * j + 1)))),
     .alu .xor dst (.imm (BitVec.ofNat 32 (leaf h (2 * j))))]
  | l + 1, j, dst =>
    mux h l (2 * j) dst ++ mux h l (2 * j + 1) (muxReg l) ++
      [.alu .xor (muxReg l) (.reg dst), .alu .and (muxReg l) (slot (7 * h + l)),
       .alu .xor dst (.reg (muxReg l))]

/-- Half `h`'s tree, into `ebx`: its first subtree is kept in slot `7 h + 6`
while the second is formed. -/
def tree (h : Nat) : List Instr :=
  mux h 5 0 .eax ++ [.store (at_ .ebp (4 * (7 * h + 6))) .eax] ++ mux h 5 1 .eax ++
    [.mov .ebx (slot (7 * h + 6)), .alu .xor .ebx (.reg .eax), .alu .and .ebx (slot (7 * h + 5)),
     .alu .xor .ebx (slot (7 * h + 6))]

/-- The S-boxes: each half's outputs to slot `14 + h`. -/
def sboxes : List Instr :=
  tree 0 ++ [.store (at_ .ebp (4 * 14)) .ebx] ++ tree 1 ++ [.store (at_ .ebp (4 * 15)) .ebx]

/-- Bit `u` of the S-boxes' outputs is bit `outPos u` of half `outHalf u`. -/
def outHalf (u : Nat) : Nat := if u / 4 < 4 then 0 else 1
def outPos (u : Nat) : Nat := 6 * (u / 4 % 4) + off (7 - u / 4) (u % 4)

/-- `L ⊕ P(S)` into `edi`, and `L` and `R` exchanged. -/
def output : List Instr :=
  [.mov .edi (slot slotL)] ++
  linCode (slot 14) .edi .ecx false
    (groups (fun j => if j < 32 ∧ outHalf (pSrc j) = 0 then some (outPos (pSrc j)) else none) 32) ++
  linCode (slot 15) .edi .ecx false
    (groups (fun j => if j < 32 ∧ outHalf (pSrc j) = 1 then some (outPos (pSrc j)) else none) 32) ++
  [.mov .eax (slot slotR), .store (at_ .ebp (4 * slotL)) .eax, .store (at_ .ebp (4 * slotR)) .edi]

/-- One round: `(L, R) := (R, L ⊕ f(R, K))`. -/
def round : List Instr := inputs ++ sboxes ++ output

/-! ## The block -/

/-- The next round key, and the round counter decremented (ZF set at 0). -/
def roundTail : List Instr :=
  [.mov .eax (slot slotStep), .alu .add .esi (.reg .eax), .mov .eax (slot slotRounds), .alu .sub .eax (.imm 1),
   .store (at_ .ebp (4 * slotRounds)) .eax]

/-- Sixteen rounds, with the round keys from `[esi]` on, a step apart. -/
def pass : Prog isa :=
  .seq (.block [.mov .eax (.imm 16), .store (at_ .ebp (4 * slotRounds)) .eax])
    (.loop (.block (round ++ roundTail)) .ne)

/-- Between passes: `esi` to the next pass's first round key (`128 − step`
on), the step negated, `L` and `R` exchanged, and the pass counter
decremented (ZF set at 0). -/
def passTail : List Instr :=
  [.mov .ecx (slot slotStep), .mov .eax (.imm 128), .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
   .mov .eax (.imm 0), .alu .sub .eax (.reg .ecx), .store (at_ .ebp (4 * slotStep)) .eax,
   .mov .eax (slot slotL), .mov .ecx (slot slotR), .store (at_ .ebp (4 * slotL)) .ecx,
   .store (at_ .ebp (4 * slotR)) .eax,
   .mov .eax (slot slotPasses), .alu .sub .eax (.imm 1), .store (at_ .ebp (4 * slotPasses)) .eax]

/-- `IP` of the block in slots 0 (its high word) and 1 (its low word): its
high half into `L`, its low half into `R`. -/
def ipCode : List Instr :=
  linCode (slot 0) .ecx .ebx true
    (groups (fun t => if t < 32 ∧ 32 ≤ ipSrc (32 + t) then some (ipSrc (32 + t) - 32) else none) 32) ++
  linCode (slot 1) .ecx .ebx false
    (groups (fun t => if t < 32 ∧ ipSrc (32 + t) < 32 then some (ipSrc (32 + t)) else none) 32) ++
  [.store (at_ .ebp (4 * slotL)) .ecx] ++
  linCode (slot 0) .ecx .ebx true
    (groups (fun t => if t < 32 ∧ 32 ≤ ipSrc t then some (ipSrc t - 32) else none) 32) ++
  linCode (slot 1) .ecx .ebx false
    (groups (fun t => if t < 32 ∧ ipSrc t < 32 then some (ipSrc t) else none) 32) ++
  [.store (at_ .ebp (4 * slotR)) .ecx]

/-- `IP⁻¹(R ‖ L)` into slots 0 (high word) and 1 (low word), with `R` in
slot `L` and `L` in slot `R` (after the last pass's exchange). -/
def fpCode : List Instr :=
  linCode (slot slotL) .ecx .ebx true
    (groups (fun t => if t < 32 ∧ 32 ≤ fpSrc (32 + t) then some (fpSrc (32 + t) - 32) else none) 32) ++
  linCode (slot slotR) .ecx .ebx false
    (groups (fun t => if t < 32 ∧ fpSrc (32 + t) < 32 then some (fpSrc (32 + t)) else none) 32) ++
  [.store (at_ .ebp 0) .ecx] ++
  linCode (slot slotL) .ecx .ebx true
    (groups (fun t => if t < 32 ∧ 32 ≤ fpSrc t then some (fpSrc t - 32) else none) 32) ++
  linCode (slot slotR) .ecx .ebx false
    (groups (fun t => if t < 32 ∧ fpSrc t < 32 then some (fpSrc t) else none) 32) ++
  [.store (at_ .ebp 4) .ecx]

/-- TDEA encryption (`E_K3(D_K2(E_K1(x)))`) of the block `x` in `eax:edx`
(its high and low words), into `eax:edx`, with the key schedule at `esi`:
the passes share one `IP` and one `IP⁻¹`, which cancel between them. `esi`
is restored. -/
def block : Prog isa :=
  .seq (.block ([.store (at_ .ebp 0) .eax, .store (at_ .ebp 4) .edx] ++ ipCode ++
      [.mov .eax (.imm 3), .store (at_ .ebp (4 * slotPasses)) .eax, .mov .eax (.imm 8),
       .store (at_ .ebp (4 * slotStep)) .eax]))
    (.seq (.loop (.seq pass (.block passTail)) .ne)
      (.block ([.alu .sub .esi (.imm 504)] ++ fpCode ++ [.mov .eax (slot 0), .mov .edx (slot 1)])))

/-! ## The key schedule -/

/-- The sixteen round keys of the DES key at `[esi]` (its high word, then
its low word), to `[edi + 8 j]` (the low word) and `[edi + 8 j + 4]` (the
high word). -/
def roundKeys : List Instr :=
  (List.range 16).flatMap fun j =>
    let w (lo : Nat) (hi : Bool) : Nat → Option Nat := fun q =>
      if q < (if lo = 0 then 32 else 16) ∧ (32 ≤ rkSrc j (lo + q)) = hi then
        some (if hi then rkSrc j (lo + q) - 32 else rkSrc j (lo + q)) else none
    linCode (.mem (at_ .esi 0)) .ecx .ebx true (groups (w 0 true) 32) ++
      linCode (.mem (at_ .esi 4)) .ecx .ebx false (groups (w 0 false) 32) ++ [.store (at_ .edi (8 * j)) .ecx] ++
    linCode (.mem (at_ .esi 0)) .ecx .ebx true (groups (w 32 true) 32) ++
      linCode (.mem (at_ .esi 4)) .ecx .ebx false (groups (w 32 false) 32) ++
      [.store (at_ .edi (8 * j + 4)) .ecx]

end VG.Impl.CmacTripleDes.X86
