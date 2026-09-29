import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Impl.Sha3.Tables
import VerifiedGarbage.Impl.Sha512.X86

/-!
# Keccak-f[1600]: x86 (32-bit) implementation

`vg_keccak_f1600(state, scratch)`, cdecl: the arguments are at `[esp + 4]`
and `[esp + 8]`.

The same structure as the x86-64 and ARMv7 implementations, with each 64-bit
lane a pair of 32-bit words, the low one first (as in memory:
little-endian). With only seven usable registers, the lanes live in memory:
`esi` points to `state` and `edi` to `scratch` throughout, `ebp` to the
current round's constant, and `eax`, `edx` (a lane's low and high halves)
and `ecx` are the temporaries. `scratch` (512 bytes) is laid out as:

* `[0, 200)`: a second state, which the rounds alternate with `state`: each
  round reads one (`src`) and writes the other (`dst`), so after the 24
  rounds the result is back in `state`;
* `[200, 392)`: the 24 round constants, stored by the prologue;
* `[392, 404)`: the saved `esi`, `edi` and `ebp` (`ebx` is never written);
* `[408, 448)`: the five column parities `C[x]` (θ), and then the five lanes
  `B[x]` of `π(ρ(θ(A)))` of the plane being computed;
* `[448, 488)`: the five `D[x]`.

A round computes `C` and then `D` into `scratch`; then, for each plane `y`
of the output, the lanes `B[x]` of that plane, and stores
`B[x] ⊕ (¬B[x+1] ∧ B[x+2])` (χ, and ι for lane 0) to `dst`, a half at a
time. The model has no 64-bit rotation and no left shift: a lane rotated
right by `32` is its halves swapped, which the loads do; one rotated right by
`0 < m < 32` is each half rotated right by `m` (`ror`), with the `m` top bits
of the two halves exchanged (masked with `and`, and exchanged with `xor`).

Every address is a pointer plus a constant or the round constant pointer,
which only depends on the pointers, and the only branch is the round loop's,
which depends only on the pointers, so only the pointers can affect timing.
The loop runs two rounds per iteration, so that `esi` and `edi` are the same
source and destination of the same rounds on every iteration.
-/

namespace VG.Impl.Sha3.X86

open VG.X86
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Impl.Sha512.X86 (at_ lo hi)

/-- `++`, grouping to the right. The kernel evaluates the code (for the
constant-time analysis), and `(a ++ b) ++ c` has it copy `a` twice. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- The offset in `scratch` of `C[x]`, and then of `B[x]`. -/
def cOff (x : Nat) : Nat := 408 + 8 * x

/-- The offset in `scratch` of `D[x]`. -/
def dOff (x : Nat) : Nat := 448 + 8 * x

/-- The offsets of the halves of a lane loaded into `(eax, edx)`: swapped (the
lane rotated by 32) if `sw`. -/
def sLo (sw : Bool) : Nat := if sw then 4 else 0
def sHi (sw : Bool) : Nat := if sw then 0 else 4

/-- `(eax, edx) :=` the lane at `[b + o]`, its halves swapped if `sw`. -/
def ld2 (sw : Bool) (b : Reg) (o : Nat) : List Instr :=
  [.mov .eax (.mem (at_ b (o + sLo sw))), .mov .edx (.mem (at_ b (o + sHi sw)))]

/-- `(eax, edx) ^=` the lane at `[b + o]`, its halves swapped if `sw`. -/
def xor2 (sw : Bool) (b : Reg) (o : Nat) : List Instr :=
  [.alu .xor .eax (.mem (at_ b (o + sLo sw))), .alu .xor .edx (.mem (at_ b (o + sHi sw)))]

/-- Store `(eax, edx)` as the lane at `[b + o]`. -/
def st2 (b : Reg) (o : Nat) : List Instr := [.store (at_ b o) .eax, .store (at_ b (o + 4)) .edx]

/-- The mask of the top `m` bits of a word. -/
def topMask (m : Nat) : BitVec 32 := BitVec.allOnes 32 <<< (32 - m)

/-- Rotate the lane in `(eax, edx)` right by `m < 32`: rotate each half, and
exchange their top `m` bits (with `ecx` as a temporary). -/
def rot (m : Nat) : List Instr :=
  if m = 0 then [] else
    [.shift .ror .eax m, .shift .ror .edx m, .mov .ecx (.reg .eax), .alu .xor .ecx (.reg .edx),
      .alu .and .ecx (.imm (topMask m)), .alu .xor .eax (.reg .ecx), .alu .xor .edx (.reg .ecx)]

/-- `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`, half `h` (`0` or `4`), from the state at `src`. -/
def colHalf (src : Reg) (x h : Nat) : List Instr :=
  [.mov .eax (.mem (at_ src (8 * x + h))), .alu .xor .eax (.mem (at_ src (8 * (x + 5) + h))),
    .alu .xor .eax (.mem (at_ src (8 * (x + 10) + h))), .alu .xor .eax (.mem (at_ src (8 * (x + 15) + h))),
    .alu .xor .eax (.mem (at_ src (8 * (x + 20) + h))), .store (at_ .edi (cOff x + h)) .eax]

def column (src : Reg) (x : Nat) : List Instr := colHalf src x 0 +++ colHalf src x 4

/-- `D[x] = ROTR⁶³(C[x + 1]) ⊕ C[x - 1]`: the halves of `C[x + 1]` swapped
(`ROTR³²`), rotated right by 31. -/
def dcol (x : Nat) : List Instr :=
  ld2 true .edi (cOff ((x + 1) % 5)) +++ rot 31 +++ xor2 false .edi (cOff ((x + 4) % 5)) +++
    st2 .edi (dOff x)

/-- Whether the lane `j`'s rotation by ρ swaps its halves: `ROTLʳ` with
`0 < r < 32` is `ROTR^(32 - r)` of the lane rotated by 32. -/
def swp (j : Nat) : Bool := 0 < rhoOff j && rhoOff j < 32

/-- The rest of the rotation, below 32. -/
def rotAmt (j : Nat) : Nat :=
  if rhoOff j = 0 then 0 else if rhoOff j < 32 then 32 - rhoOff j else 64 - rhoOff j

/-- `B[x] = ROTL^ρ(A[piSrc x y] ⊕ D[(x + 3y) mod 5])` for plane `y`, stored in `scratch`. -/
def laneB (src : Reg) (x y : Nat) : List Instr :=
  ld2 (swp (piSrc x y)) src (8 * piSrc x y) +++
    xor2 (swp (piSrc x y)) .edi (dOff ((x + 3 * y) % 5)) +++ rot (rotAmt (piSrc x y)) +++
    st2 .edi (cOff x)

/-- Half `h` of lane `(x, y)` of the output: `B[x] ⊕ (¬B[x+1] ∧ B[x+2])`, and
for lane 0 the round constant at `ebp`, stored at `[dst + 8(x + 5y) + h]`.
(`¬` is an XOR with all ones.) -/
def chiHalf (dst : Reg) (x y h : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (cOff ((x + 1) % 5) + h))), .alu .xor .eax (.imm (BitVec.allOnes 32)),
    .alu .and .eax (.mem (at_ .edi (cOff ((x + 2) % 5) + h))),
    .alu .xor .eax (.mem (at_ .edi (cOff x + h)))] +++
    (if x = 0 ∧ y = 0 then [.alu .xor .eax (.mem (at_ .ebp h))] else []) +++
    [.store (at_ dst (8 * (x + 5 * y) + h)) .eax]

def chi (dst : Reg) (x y : Nat) : List Instr := chiHalf dst x y 0 +++ chiHalf dst x y 4

/-- Plane `y` of the output. -/
def plane (src dst : Reg) (y : Nat) : List Instr :=
  (List.range 5).flatMap (fun x => laneB src x y) +++ (List.range 5).flatMap (fun x => chi dst x y)

/-- One round from `src` to `dst`; then advance to the next round constant. -/
def round (src dst : Reg) : List Instr :=
  (List.range 5).flatMap (column src) +++ (List.range 5).flatMap dcol +++
    (List.range 5).flatMap (plane src dst) +++ [.alu .add .ebp (.imm 8)]

/-- Two rounds, and set ZF after the last. -/
def body : List Instr :=
  round .esi .edi +++ round .edi .esi +++
    [.mov .eax (.reg .ebp), .alu .sub .eax (.reg .edi), .alu .cmp .eax (.imm 392)]

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.esi, 392), (.edi, 396), (.ebp, 400)]

/-- Round constant `k`, stored at `scratch + 200 + 8k`. -/
def rcStore (k : Nat) : List Instr :=
  [.mov .eax (.imm (lo (Spec.Sha3.RC k))), .store (at_ .edi (200 + 8 * k)) .eax,
    .mov .eax (.imm (hi (Spec.Sha3.RC k))), .store (at_ .edi (204 + 8 * k)) .eax]

/-- Save the registers, load the arguments, store the round constants, and
point `ebp` at the first. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 4))] +++
    saved.map (fun (r, d) => .store (at_ .eax d) r) +++
    [.mov .edi (.reg .eax), .mov .esi (.reg .ecx)] +++ (List.range 24).flatMap rcStore +++
    [.mov .ebp (.reg .edi), .alu .add .ebp (.imm 200)]

/-- Restore the registers (`edi`, the base, last). -/
def restore : List Instr :=
  [.mov .esi (.mem (at_ .edi 392)), .mov .ebp (.mem (at_ .edi 400)), .mov .edi (.mem (at_ .edi 396))]

def permute : Prog isa :=
  .seq (.block prologue) (.seq (.loop (.block body) .ne) (.block restore))

end VG.Impl.Sha3.X86
