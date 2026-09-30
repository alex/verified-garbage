import VerifiedGarbage.TCB.X86_64.Isa

/-!
# ML-DSA on x86-64: rounding and hints

`vg_mldsa_power2round`, `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint` and `vg_mldsa_use_hint` each run
one loop over the 256 coefficients (`mapLoop`), with `rcx` counting down
from 256: iteration `rcx` handles coefficient `rcx - 1` of each polynomial
`p`, at `[p + 4·rcx - 4]` (`cf p`). There is no branch on data: a
conditional step is a subtraction whose borrow `sbb` turns into a mask
(`condAdd`), and `Decompose` divides by `2γ₂` with a multiplication and
shifts, as the reference implementation does (`hbRaw`):
`f = ⌊(⌊(a + 127)/2⁷⌋ · M + 2^(S-1)) / 2^S⌋` for `(M, S)` = `(1025, 22)` if
`γ₂ = (q - 1)/32` and `(11275, 24)` if `γ₂ = (q - 1)/88`, which is
`⌊(a + γ₂ - 1)/(2γ₂)⌋` for every `a < q`; then `r₁ = f mod m` for
`m = (q - 1)/(2γ₂)` (16 or 44) is one conditional subtraction of `m`, as
`f ≤ m` (`hb`). `γ₂` is a public argument: the functions that take it
branch on it once, to one loop for each value.

* `power2Round(t = rdi, t1 = rsi, t0 = rdx)`: `x = a + 4095`, `t1 = x >> 13`
  and `t0 = (x mod 2¹³) - 4095`, plus `q` if negative.
* `highBits(r = rdi, gamma2 = esi, out = rdx → r10)`: `r₁`.
* `lowBits(r = rdi, gamma2 = esi, out = rdx → r10)`: `a - r₁ · 2γ₂`, plus
  `q` if negative.
* `normLt(f = rdi, bound = esi)`: the top bit of `r9` stays set while every
  coefficient `a` so far has `a < bound` or `q - a < bound` (both
  differences, in 64 bits, negative for one of them); it is the result.
* `makeHint(z = rdi, r = rsi, gamma2 = edx, h = rcx → r10)`: `r₁` of `r` (kept
  in `r11`) and of `r + z mod q`, xored, is nonzero (`(x + 63) >> 6`, as
  `x < 64`) exactly when the hint is 1; `r9` counts the 1s.
* `useHint(h = rdi, r = rsi, gamma2 = edx, out = rcx → r10)`: `(f + m + δ)
  mod m` by two conditional subtractions of `m`, for `δ` 0 if the hint is 0
  and else 1 if `f · 2γ₂ < a` (`r₀ > 0`), -1 otherwise, as masks.
-/

namespace VG.Impl.MlDsa.X86_64.Round

open VG.X86_64

/-- `[p + 4·rcx - 4]`: coefficient `rcx - 1` of the polynomial at `p`. -/
def cf (p : Reg) : MemOp := { base := p, index := some .rcx, scale := 4, disp := -4 }

/-- `q = 8380417`, as an immediate. -/
def qImm : BitVec 32 := 8380417

/-- `r ← r - x`, plus `k` if that borrows, with `m` as the mask. -/
def condAdd (r : Reg) (x : Src) (m : Reg) (k : BitVec 32) : List Instr :=
  [.alu .sub r x, .alu .sbb m (.reg m), .alu .and m (.imm k), .alu .add r (.reg m)]

/-- The loop over the coefficients: `body`, then `rcx` counts down. -/
def mapLoop (body : List Instr) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block (body ++ [.alu .sub .rcx (.imm 1)])) .ne)

/-! ## `Decompose` -/

/-- The multiplier `M`. -/
def hbMul (g : Nat) : Nat := if g = 261888 then 1025 else 11275

/-- The shift `S`. -/
def hbShift (g : Nat) : Nat := if g = 261888 then 22 else 24

/-- `2^(S-1)`. -/
def hbAdd (g : Nat) : Nat := if g = 261888 then 2 ^ 21 else 2 ^ 23

/-- `m = (q - 1)/(2γ₂)`. -/
def hbM (g : Nat) : Nat := if g = 261888 then 16 else 44

/-- `rax ← f` for `a = rax`. Uses `r8` and `rdx`. -/
def hbRaw (g : Nat) : List Instr :=
  [.alu .add .rax (.imm 127), .shift .shr .rax 7, .mov32 .r8 (.imm (BitVec.ofNat 32 (hbMul g))), .mul .r8,
    .alu .add .rax (.imm (BitVec.ofNat 32 (hbAdd g))), .shift .shr .rax (hbShift g)]

/-- `rax ← r₁ = f mod m` for `a = rax`. Uses `r8` and `rdx`. -/
def hb (g : Nat) : List Instr :=
  hbRaw g ++ condAdd .rax (.imm (BitVec.ofNat 32 (hbM g))) .r8 (BitVec.ofNat 32 (hbM g))

/-- The values of `γ₂`: `(q - 1)/32` and `(q - 1)/88`. -/
def g32 : Nat := 261888
def g88 : Nat := 95232

/-! ## The functions -/

def p2rBody : List Instr :=
  [.mov32 .rax (.mem (cf .rdi)), .alu .add .rax (.imm 4095), .mov .r8 (.reg .rax), .shift .shr .r8 13,
    .store32 (cf .rsi) .r8, .alu .and .rax (.imm 8191)] ++ condAdd .rax (.imm 4095) .r9 qImm ++
    [.store32 (cf .rdx) .rax]

def power2Round : Prog isa := mapLoop p2rBody

/-- `γ₂` (in `rsi` or `rdx`), zero-extended, compared with `(q - 1)/32`. -/
def gammaCmp (r : Reg) : List Instr := [.mov32 r (.reg r), .alu32 .cmp r (.imm (BitVec.ofNat 32 g32))]

def hbBody (g : Nat) : List Instr := [.mov32 .rax (.mem (cf .rdi))] ++ hb g ++ [.store32 (cf .r10) .rax]

def highBits : Prog isa :=
  .seq (.block (gammaCmp .rsi ++ [.mov .r10 (.reg .rdx)])) (.ite .e (mapLoop (hbBody g32)) (mapLoop (hbBody g88)))

def lbBody (g : Nat) : List Instr :=
  [.mov32 .rax (.mem (cf .rdi)), .mov .r11 (.reg .rax)] ++ hb g ++
    [.mov32 .r8 (.imm (BitVec.ofNat 32 (2 * g))), .mul .r8] ++ condAdd .r11 (.reg .rax) .r8 qImm ++
    [.store32 (cf .r10) .r11]

def lowBits : Prog isa :=
  .seq (.block (gammaCmp .rsi ++ [.mov .r10 (.reg .rdx)])) (.ite .e (mapLoop (lbBody g32)) (mapLoop (lbBody g88)))

def nlBody : List Instr :=
  [.mov32 .rax (.mem (cf .rdi)), .mov32 .rdx (.imm qImm), .alu .sub .rdx (.reg .rax), .alu .sub .rax (.reg .rsi),
    .alu .sub .rdx (.reg .rsi), .alu .or .rax (.reg .rdx), .alu .and .r9 (.reg .rax)]

def normLt : Prog isa :=
  .seq (.block [.mov32 .rsi (.reg .rsi), .mov .r9 (.imm 0xFFFFFFFF)])
    (.seq (mapLoop nlBody) (.block [.mov .rax (.reg .r9), .shift .shr .rax 63]))

def mhBody (g : Nat) : List Instr :=
  [.mov32 .rax (.mem (cf .rsi))] ++ hb g ++
    [.mov .r11 (.reg .rax), .mov32 .rax (.mem (cf .rsi)), .alu32 .add .rax (.mem (cf .rdi))] ++
    condAdd .rax (.imm qImm) .r8 qImm ++ hb g ++
    [.alu .xor .rax (.reg .r11), .alu .add .rax (.imm 63), .shift .shr .rax 6, .store32 (cf .r10) .rax,
      .alu .add .r9 (.reg .rax)]

def makeHint : Prog isa :=
  .seq (.block (gammaCmp .rdx ++ [.mov .r10 (.reg .rcx), .mov32 .r9 (.imm 0)]))
    (.seq (.ite .e (mapLoop (mhBody g32)) (mapLoop (mhBody g88))) (.block [.mov .rax (.reg .r9)]))

def uhBody (g : Nat) : List Instr :=
  [.mov32 .rax (.mem (cf .rsi)), .mov .r11 (.reg .rax)] ++ hbRaw g ++
    [.mov .r9 (.reg .rax), .mov32 .r8 (.imm (BitVec.ofNat 32 (2 * g))), .mul .r8, .alu .sub .rax (.reg .r11),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 2), .alu .sub .rax (.imm 1),
      .mov32 .r11 (.mem (cf .rdi)), .mov32 .r8 (.imm 0), .alu .sub .r8 (.reg .r11), .alu .sbb .r8 (.reg .r8),
      .alu .and .rax (.reg .r8), .alu .add .rax (.reg .r9), .alu .add .rax (.imm (BitVec.ofNat 32 (hbM g)))] ++
    condAdd .rax (.imm (BitVec.ofNat 32 (hbM g))) .r8 (BitVec.ofNat 32 (hbM g)) ++
    condAdd .rax (.imm (BitVec.ofNat 32 (hbM g))) .r8 (BitVec.ofNat 32 (hbM g)) ++
    [.store32 (cf .r10) .rax]

def useHint : Prog isa :=
  .seq (.block (gammaCmp .rdx ++ [.mov .r10 (.reg .rcx)])) (.ite .e (mapLoop (uhBody g32)) (mapLoop (uhBody g88)))

end VG.Impl.MlDsa.X86_64.Round
