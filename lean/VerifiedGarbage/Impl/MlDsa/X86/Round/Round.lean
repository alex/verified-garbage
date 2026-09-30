import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-DSA on x86 (32-bit): rounding and hints

`vg_mldsa_power2round`, `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint` and `vg_mldsa_use_hint` are leaves
(`Impl.MlKem.X86.leaf`, which saves the caller's `ebx`, `esi`, `edi` and
`ebp`; the arguments are then at `[esp + 20]`, `[esp + 24]`, …), each one
loop over the 256 coefficients, with a pointer register at coefficient `i`
of each polynomial. There is no branch on data: a conditional step is a
subtraction whose borrow `sbb` turns into a mask (`condAdd`), and
`Decompose` divides by `2γ₂` with a multiplication and shifts, as the
reference implementation and x86-64 do (`hbRaw`):
`f = ⌊(⌊(a + 127)/2⁷⌋ · M + 2^(S-1)) / 2^S⌋` for `(M, S)` = `(1025, 22)` if
`γ₂ = (q - 1)/32` and `(11275, 24)` if `γ₂ = (q - 1)/88`, which is
`⌊(a + γ₂ - 1)/(2γ₂)⌋` for every `a < q` (every intermediate value is less
than `2³²`); then `r₁ = f mod m` for `m = (q - 1)/(2γ₂)` (16 or 44) is one
conditional subtraction of `m`, as `f ≤ m` (`hb`). `Decompose` uses only
`eax` and `edx`. `γ₂` is a public argument: the functions that take it
branch on it once, to one loop for each value.

The loops of `power2Round`, `highBits`, `lowBits` and `normLt` count the
coefficients left in `ecx`; `makeHint` and `useHint` need `ecx`, so they
store the end of their output, `out + 1024`, in the argument slot of `γ₂`
(which they no longer need), and compare their output pointer with it.

* `power2Round(t, t1, t0)` (`esi`, `edi`, `ebp`): `x = a + 4095`,
  `t1 = x >> 13` and `t0 = (x mod 2¹³) - 4095`, plus `q` if negative.
* `highBits(r, gamma2, out)` (`esi`, `edi`): `r₁`.
* `lowBits(r, gamma2, out)` (`esi`, `edi`): `a - r₁ · 2γ₂`, plus `q` if
  negative (`a` kept in `ebx`).
* `normLt(f, bound)` (`esi`; `bound` in `ebx`): `ebp` stays all ones while
  every coefficient `a` so far has `a < bound` or `q - a < bound` (both
  comparisons borrow into masks); its low bit is the result.
* `makeHint(z, r, gamma2, h)` (`esi`, `edi`, `ebp`): `r₁` of `r` (kept in
  `ebx`) and of `r + z mod q`, xored, is nonzero (`(x + 63) >> 6`, as
  `x < 64`) exactly when the hint is 1; `ecx` counts the 1s.
* `useHint(h, r, gamma2, out)` (`esi`, `edi`, `ebp`): `(f + m + δ) mod m`
  by two conditional subtractions of `m`, for `δ` 0 if the hint is 0 and
  else 1 if `f · 2γ₂ < a` (`r₀ > 0`), -1 otherwise, as masks (`a` in `ebx`,
  `f` in `ecx`).
-/

namespace VG.Impl.MlDsa.X86.Round

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf)

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `q = 8380417`, as an immediate. -/
def qImm : BitVec 32 := 8380417

/-- `r ← r - x`, plus `k` if that borrows, with `t` as the mask. -/
def condAdd (r : Reg) (x : Src) (t : Reg) (k : BitVec 32) : List Instr :=
  [.alu .sub r x, .alu .sbb t (.reg t), .alu .and t (.imm k), .alu .add r (.reg t)]

/-! ## `Decompose` -/

/-- The multiplier `M`. -/
def dMul (g : Nat) : Nat := if g = 261888 then 1025 else 11275

/-- The shift `S`. -/
def dShift (g : Nat) : Nat := if g = 261888 then 22 else 24

/-- `2^(S-1)`. -/
def dAdd (g : Nat) : Nat := if g = 261888 then 2 ^ 21 else 2 ^ 23

/-- `m = (q - 1)/(2γ₂)`. -/
def dMod (g : Nat) : Nat := if g = 261888 then 16 else 44

/-- `eax ← f` for `a = eax`. Uses `edx`. -/
def hbRaw (g : Nat) : List Instr :=
  [.alu .add .eax (.imm 127), .shift .shr .eax 7, .mov .edx (.imm (BitVec.ofNat 32 (dMul g))), .mul .edx,
    .alu .add .eax (.imm (BitVec.ofNat 32 (dAdd g))), .shift .shr .eax (dShift g)]

/-- `eax ← r₁ = f mod m` for `a = eax`. Uses `edx`. -/
def hb (g : Nat) : List Instr :=
  hbRaw g +++ condAdd .eax (.imm (BitVec.ofNat 32 (dMod g))) .edx (BitVec.ofNat 32 (dMod g))

/-- The values of `γ₂`: `(q - 1)/32` and `(q - 1)/88`. -/
def g32 : Nat := 261888
def g88 : Nat := 95232

/-! ## The loops -/

/-- The loop counting 256 coefficients down in `ecx`. -/
def cntLoop (body : List Instr) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 256)]) (.loop (.block body) .ne)

/-- Store `eax` to the output at `ebp`, advance the pointers, and compare
the output pointer with the end of the output (in the slot of `γ₂`). -/
def endTail : List Instr :=
  [.store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4),
    .alu .cmp .ebp (.mem (at_ .esp 28))]

/-- Store `eax` to the output at `edi`, advance the pointers, count down. -/
def cntTail : List Instr :=
  [.store (at_ .edi 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]

/-! ## `power2Round` -/

def p2rBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.imm 4095), .mov .edx (.reg .eax), .shift .shr .edx 13,
    .store (at_ .edi 0) .edx, .alu .and .eax (.imm 8191)] +++ condAdd .eax (.imm 4095) .edx qImm +++
  [.store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4),
    .alu .sub .ecx (.imm 1)]

/-- `esi = t`, `edi = t1`, `ebp = t0`. -/
def p2rInit : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 24)), .mov .ebp (.mem (at_ .esp 28))]

def power2Round : Prog isa := leaf (.seq (.block p2rInit) (cntLoop p2rBody))

/-! ## `highBits` and `lowBits` -/

/-- `esi = r`, `edi = out`, and `γ₂` compared with `(q - 1)/32`. -/
def bitsInit : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 28)), .mov .eax (.mem (at_ .esp 24)),
    .alu .cmp .eax (.imm (BitVec.ofNat 32 g32))]

/-- `eax ← r₁` of `[esi]`. -/
def hbCore (g : Nat) : List Instr := .mov .eax (.mem (at_ .esi 0)) :: hb g

/-- `eax ← r₀` of `[esi]`, modulo `q`. -/
def lbCore (g : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mov .ebx (.reg .eax)] +++ hb g +++
  [.mov .edx (.imm (BitVec.ofNat 32 (2 * g))), .mul .edx] +++ condAdd .ebx (.reg .eax) .edx qImm +++
  [.mov .eax (.reg .ebx)]

def highBits : Prog isa :=
  leaf (.seq (.block bitsInit) (.ite .e (cntLoop (hbCore g32 +++ cntTail)) (cntLoop (hbCore g88 +++ cntTail))))

def lowBits : Prog isa :=
  leaf (.seq (.block bitsInit) (.ite .e (cntLoop (lbCore g32 +++ cntTail)) (cntLoop (lbCore g88 +++ cntTail))))

/-! ## `normLt` -/

def nlBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mov .edx (.imm qImm), .alu .sub .edx (.reg .eax), .alu .cmp .eax (.reg .ebx),
    .alu .sbb .eax (.reg .eax), .alu .cmp .edx (.reg .ebx), .alu .sbb .edx (.reg .edx), .alu .or .eax (.reg .edx),
    .alu .and .ebp (.reg .eax), .alu .add .esi (.imm 4), .alu .sub .ecx (.imm 1)]

/-- `esi = f`, `ebx = bound`, `ebp` all ones. -/
def nlInit : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .ebx (.mem (at_ .esp 24)), .mov .ebp (.imm 0xFFFFFFFF)]

def normLt : Prog isa :=
  leaf (.seq (.block nlInit) (.seq (cntLoop nlBody) (.block [.mov .eax (.reg .ebp), .alu .and .eax (.imm 1)])))

/-! ## `makeHint` and `useHint` -/

/-- `esi`, `edi` and `ebp` at the first, second and fourth arguments, the end
of the output in the slot of `γ₂`, `ecx = 0`, and `γ₂` compared with
`(q - 1)/32`. -/
def hintInit : List Instr :=
  [.mov .edx (.mem (at_ .esp 28)), .mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 24)),
    .mov .ebp (.mem (at_ .esp 32)), .mov .eax (.reg .ebp), .alu .add .eax (.imm 1024), .store (at_ .esp 28) .eax,
    .mov .ecx (.imm 0), .alu .cmp .edx (.imm (BitVec.ofNat 32 g32))]

/-- `eax ← MakeHint` of `[esi]` and `[edi]`, and `ecx` counts it. -/
def mhCore (g : Nat) : List Instr :=
  .mov .eax (.mem (at_ .edi 0)) :: hb g +++
  [.mov .ebx (.reg .eax), .mov .eax (.mem (at_ .edi 0)), .alu .add .eax (.mem (at_ .esi 0))] +++
  condAdd .eax (.imm qImm) .edx qImm +++ hb g +++
  [.alu .xor .eax (.reg .ebx), .alu .add .eax (.imm 63), .shift .shr .eax 6, .alu .add .ecx (.reg .eax)]

/-- `eax ← UseHint` of `[esi]` and `[edi]`. -/
def uhCore (g : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi 0)), .mov .ebx (.reg .eax)] +++ hbRaw g +++
  [.mov .ecx (.reg .eax), .mov .edx (.imm (BitVec.ofNat 32 (2 * g))), .mul .edx, .alu .sub .eax (.reg .ebx),
    .alu .sbb .eax (.reg .eax), .alu .and .eax (.imm 2), .alu .sub .eax (.imm 1), .mov .ebx (.imm 0),
    .alu .sub .ebx (.mem (at_ .esi 0)), .alu .sbb .ebx (.reg .ebx), .alu .and .eax (.reg .ebx),
    .alu .add .eax (.reg .ecx), .alu .add .eax (.imm (BitVec.ofNat 32 (dMod g)))] +++
  condAdd .eax (.imm (BitVec.ofNat 32 (dMod g))) .edx (BitVec.ofNat 32 (dMod g)) +++
  condAdd .eax (.imm (BitVec.ofNat 32 (dMod g))) .edx (BitVec.ofNat 32 (dMod g))

def makeHint : Prog isa :=
  leaf (.seq (.block hintInit) (.seq (.ite .e (.loop (.block (mhCore g32 +++ endTail)) .ne)
    (.loop (.block (mhCore g88 +++ endTail)) .ne)) (.block [.mov .eax (.reg .ecx)])))

def useHint : Prog isa :=
  leaf (.seq (.block hintInit) (.ite .e (.loop (.block (uhCore g32 +++ endTail)) .ne)
    (.loop (.block (uhCore g88 +++ endTail)) .ne)))

end VG.Impl.MlDsa.X86.Round
