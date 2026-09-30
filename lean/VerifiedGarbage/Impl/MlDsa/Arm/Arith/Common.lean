import VerifiedGarbage.TCB.Arm.Isa

/-!
# ML-DSA on 32-bit ARM: arithmetic modulo `q`

Pieces of code that the ML-DSA functions share, for `q = 8380417 < 2²³`. The
model has only the 32-bit multiplication `mul` (the long multiplications are
left out, see `TCB/Arm/Isa.lean`), so a product of two reduced values, which
has up to 46 bits, is never formed:

* `red d t Q`: `d ← d - ⌊d / 2²³⌋ · q`, for any 32-bit `d`, with `q` in `Q`:
  as `2²³ ≡ 2¹³ - 1`, the result is congruent to `d` and at most
  `2²³ - 1 + 511 · 8191 < 1.5 · 2²³`;
* `mulz acc b t`: `acc ← b · z` modulo `q` (less than `2q`), for `b < q` and
  `z < q` whose pieces `⌊z / 2¹⁴⌋ < 2⁹`, `⌊z / 2⁷⌋ mod 2⁷` and `z mod 2⁷` are
  in `r5`, `r6` and `r7` (`zPieces`), and `q` in `r4`: by Horner's rule,
  `(((b · z₂) · 2⁷ + b · z₁) · 2⁷ + b · z₀`, reducing with `red` after each
  step, so that every intermediate value fits in 32 bits;
* `fixup d t Q`: `d ← d + q` if `d` is negative (as a two's complement
  number), with `t` as the mask: `(d >> 31) · q` is `q` or 0;
* `csub d t Q`: `d ← d mod q` for `d < 2q`, as `fixup (d - q)`.

A function that uses more registers than `r0`–`r3` and `r12` saves them in
frames on the stack, one per register (`saving`), and restores each with
the pop of its frame.
-/

namespace VG.Impl.MlDsa.Arm.Arith

open VG.Arm

/-- `r ← q = 0x7FE001`. -/
def loadQ (r : Reg) : List Instr := [.movw r 0xE001, .movt r 0x7F]

/-- `d ← d - ⌊d / 2²³⌋ · q`, with `q` in `Q` and `t` a temporary. -/
def red (d t Q : Reg) : List Instr := [.mov t (.shifted d .lsr 23), .mul t t Q, .dp .sub d d (.reg t)]

/-- `d ← d + q` if `d` is negative, with `q` in `Q` and `t` a temporary. -/
def fixup (d t Q : Reg) : List Instr := [.mov t (.shifted d .lsr 31), .mul t t Q, .dp .add d d (.reg t)]

/-- `d ← d - q`, plus `q` if that is negative: `d mod q` for `d < 2q`. -/
def csub (d t Q : Reg) : List Instr := .dp .sub d d (.reg Q) :: fixup d t Q

/-- The pieces of the word in `a`: `r5 = a >> 14`, `r6 = (a >> 7) mod 2⁷`,
`r7 = a mod 2⁷`. -/
def zPieces (a : Reg) : List Instr :=
  [.mov .r5 (.shifted a .lsr 14), .mov .r6 (.shifted a .lsl 18), .mov .r6 (.shifted .r6 .lsr 25),
   .mov .r7 (.shifted a .lsl 25), .mov .r7 (.shifted .r7 .lsr 25)]

/-- `acc ← b · z` modulo `q` (less than `2q`), for the pieces of `z` in
`r5`–`r7` and `q` in `r4`, with `t` a temporary. -/
def mulz (acc b t : Reg) : List Instr :=
  [.mul acc b .r5] ++ red acc t .r4 ++ [.mul t b .r6, .dp .add acc t (.shifted acc .lsl 7)] ++
    red acc t .r4 ++ [.mul t b .r7, .dp .add acc t (.shifted acc .lsl 7)] ++ red acc t .r4

/-- `body`, with the registers `rs` saved in a frame each around it. -/
def saving : List Reg → Prog isa → Prog isa
  | [], body => body
  | r :: rs, body => .frame (.push [r]) (saving rs body) (.pop r 4)

end VG.Impl.MlDsa.Arm.Arith
