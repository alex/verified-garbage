import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Impl.Sha3.Tables
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Impl.Sha3.X86_64

/-!
# Keccak-f[1600] on four states at once: x86-64 with AVX2

Four states in one buffer of 800 bytes, interleaved: lane `j` of state `k`
is the `u64` at byte `32 j + 8 k`, so that lane `j` of the four is one
256-bit value, and each instruction on `ymm` registers computes the same on
the four states, one in each 64-bit element.

`permute4` is a fragment (not a function: its callers inline it), with
`rdi` pointing at the states, `rsi` at a second buffer of 800 bytes, and
`rdx` at a table of the 24 round constants, each in the four elements of a
`u256` (768 bytes; `rcTable` stores it, through `rax`), and `rcx` past its
end. As the scalar implementation (`Impl/Sha3/X86_64.lean`), a round reads
one buffer (`src`, `rdi`) and writes the other (`dst`, `rsi`), then swaps
them; the loop runs two rounds per iteration, so that after the 24 rounds
the result is back at `rdi`. A round computes the five column parities
`C[x]` (θ) into `ymm0`–`ymm4`, then `D[x]` into `ymm5`–`ymm9`; then, for
each plane `y` of the output, the five lanes `B[x]` of `π(ρ(θ(A)))` in that
plane into `ymm0`–`ymm4` (a rotation left by `n` is `vpsllq`, `vpsrlq` by
`64 - n` and `vpor`, with `ymm10`), and stores `B[x] ⊕ (¬B[x+1] ∧ B[x+2])`
(χ, `vpandn`, and ι for lane 0, with `ymm11`), computed in `ymm10`, to
`dst`. It writes only `rax`, `rdx`, `rdi`, `rsi`, the flags and `ymm0`–`ymm11`.

Every address is a pointer plus a constant, and the only branch is the
round loop's, so only the pointers can affect timing.
-/

namespace VG.Impl.Sha3.X86_64.X4

open VG.X86_64
open VG.Impl.Sha3 (rhoOff piSrc)

/-- `op d, a, b` on 256 bits. -/
def vb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

/-- `op d, a, n` (a shift of each 64-bit element) on 256 bits. -/
def vsh (op : XShiftOp) (d a : XReg) (n : Nat) : Instr := .vop (.vshift op .l256 d a (BitVec.ofNat 8 n))

/-- Lane `i` of the four states at `b`, to `d`. -/
def ld (d : XReg) (b : Reg) (i : Nat) : Instr := .vmovdquLoad .l256 d (at_ b (32 * i))

/-- `r` to lane `i` of the four states at `b`. -/
def st (b : Reg) (i : Nat) (r : XReg) : Instr := .vmovdquStore .l256 (at_ b (32 * i)) r

/-- The register of `C[x]`, and then of `B[x]`. -/
def creg (x : Nat) : XReg := [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4].getD x .xmm0

/-- The register of `D[x]`. -/
def dreg (x : Nat) : XReg := [XReg.xmm5, .xmm6, .xmm7, .xmm8, .xmm9].getD x .xmm5

/-- The temporaries. -/
def T : XReg := .xmm10
def U : XReg := .xmm11

/-- `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`. -/
def column (x : Nat) : List Instr :=
  [ld (creg x) .rdi x, ld T .rdi (x + 5), vb .vpxor (creg x) (creg x) T, ld T .rdi (x + 10),
    vb .vpxor (creg x) (creg x) T, ld T .rdi (x + 15), vb .vpxor (creg x) (creg x) T, ld T .rdi (x + 20),
    vb .vpxor (creg x) (creg x) T]

/-- `D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1]`. -/
def dcol (x : Nat) : List Instr :=
  [vsh .psllq T (creg ((x + 1) % 5)) 1, vsh .psrlq U (creg ((x + 1) % 5)) 63, vb .vpor T T U,
    vb .vpxor (dreg x) T (creg ((x + 4) % 5))]

/-- `B[x] = ROTL^ρ(A[piSrc x y] ⊕ D[(x + 3y) mod 5])` for plane `y`. -/
def laneB (x y : Nat) : List Instr :=
  [ld (creg x) .rdi (piSrc x y), vb .vpxor (creg x) (creg x) (dreg ((x + 3 * y) % 5))] ++
    if rhoOff (piSrc x y) = 0 then []
    else [vsh .psllq T (creg x) (rhoOff (piSrc x y)), vsh .psrlq (creg x) (creg x) (64 - rhoOff (piSrc x y)),
      vb .vpor (creg x) (creg x) T]

/-- Lane `(x, y)` of the output: `B[x] ⊕ (¬B[x+1] ∧ B[x+2])`, and for lane 0
the round constant at `rdx`. -/
def chi (x y : Nat) : List Instr :=
  [vb .vpandn T (creg ((x + 1) % 5)) (creg ((x + 2) % 5)), vb .vpxor T T (creg x)] ++
    (if x = 0 ∧ y = 0 then [ld U .rdx 0, vb .vpxor T T U] else []) ++
    [st .rsi (x + 5 * y) T]

/-- Plane `y` of the output. -/
def plane (y : Nat) : List Instr :=
  (List.range 5).flatMap (fun x => laneB x y) ++ (List.range 5).flatMap (fun x => chi x y)

/-- One round from `rdi` to `rsi`; then swap them, and advance to the next
round constant (setting ZF after the last). -/
def round : List Instr :=
  (List.range 5).flatMap column ++ (List.range 5).flatMap dcol ++ (List.range 5).flatMap plane ++
    [.mov .rax (.reg .rdi), .mov .rdi (.reg .rsi), .mov .rsi (.reg .rax),
      .alu .add .rdx (.imm 32), .alu .cmp .rdx (.reg .rcx)]

/-- The 24 rounds, from `rdi` (and back to it), with the table at `rdx`
and its end in `rcx`. -/
def permute4 : Prog isa := .loop (.block (round ++ round)) .ne

/-- The table of the round constants at `[b + off]`, each four times,
through `rax`. -/
def rcTable (b : Reg) (off : Nat) : List Instr :=
  (List.range 24).flatMap fun k =>
    .movImm64 .rax (Spec.Sha3.RC k) :: (List.range 4).map fun i => .store (at_ b (off + 32 * k + 8 * i)) .rax

end VG.Impl.Sha3.X86_64.X4
