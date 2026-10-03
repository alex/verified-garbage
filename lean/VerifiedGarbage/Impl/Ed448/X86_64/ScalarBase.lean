import VerifiedGarbage.Impl.X448.X86_64.Adx
import VerifiedGarbage.Impl.Ed448.X86_64.Scalar
import VerifiedGarbage.Spec.Ed448

/-!
# Ed448 base-point multiplication on x86-64

`vg_ed448_scalar_base(out = rdi, scalar = rsi, scratch = rdx)`: the encoding
of `[s]B` for the 456-bit little-endian scalar `s`, without pruning.

Field elements are X448's (seven 64-bit words in the slots of the working
space, `Impl/X448/X86_64.lean`), and so is the field arithmetic: the field
multiplications `F` (the baseline's or BMI2 and ADX's), additions,
subtractions, the constant-time swap, the inversion and the full reduction.
Points are the specification's projective coordinates `(X : Y : Z)`.

The scalar's bits are expanded into bytes at `BITS` (byte `t` is bit `t`),
as X448 expands its scalar. Then, from the top bit down, the point `R`
(slots 0–2, from the neutral point) is doubled (RFC 8032 §5.2.4's doubling
formulas), `T = R + B` computed (§5.2.4's addition, `B` in slots 8–10 and
`d` in slot 11), and `T` swapped into `R` with the mask of the bit: the same
operations for every bit, whatever its value. Finally `R` is encoded
(§5.2.2): `Z` inverted, `x = X/Z` and `y = Y/Z` fully reduced, and the low
bit of `x` stored as the top bit of the 57th byte.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

namespace VG.Impl.Ed448.X86_64

open VG.X86_64
open VG.Impl.X448.X86_64 (at_ sc W w loads stores slot Field add sub cswap freeze invert BITS bitAt)

/-! ## Field programs on the slots -/

/-- A field operation on slots (X448's 64-byte slots, numbered from 0). -/
inductive FOp where
  | mul (o a b : Nat)
  | sqr (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  deriving DecidableEq, Repr

/-- The code of a field operation, with the field multiplications `F`. -/
def FOp.code (F : Field) : FOp → List Instr
  | .mul o a b => F.mul (slot o) (slot a) (slot b)
  | .sqr o a => F.sqr (slot o) (slot a)
  | .add o a b => Impl.X448.X86_64.add (slot o) (slot a) (slot b)
  | .sub o a b => Impl.X448.X86_64.sub (slot o) (slot a) (slot b)

def fieldCode (F : Field) (ops : List FOp) : List Instr := ops.flatMap (FOp.code F)

/-- `R = 2R` in slots 0–2 (RFC 8032 §5.2.4, doubling), with the temporaries
12–19: `B = (X + Y)²`, `C = X²`, `D = Y²`, `E = C + D`, `H = Z²`,
`J = E - 2H`, `X = (B - E) J`, `Y = E (C - D)`, `Z = E J`. -/
def doubleOps : List FOp := [
  .add 12 0 1, .sqr 12 12, .sqr 13 0, .sqr 14 1, .add 15 13 14, .sqr 16 2,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul 0 18 17, .sub 19 13 14, .mul 1 15 19,
  .mul 2 15 17]

/-- `T = R + Q` into slots 3–5, for `R` in slots 0–2, `Q` in slots 8–10 and
`d` in slot 11 (RFC 8032 §5.2.4, addition), with the temporaries 12–20:
`A = Z₁Z₂`, `B = A²`, `C = X₁X₂`, `D = Y₁Y₂`, `E = dCD`, `F = B - E`,
`G = B + E`, `H = (X₁ + Y₁)(X₂ + Y₂)`, `X₃ = AF(H - C - D)`,
`Y₃ = AG(D - C)`, `Z₃ = FG`. -/
def addOps : List FOp := [
  .mul 12 2 10, .sqr 13 12, .mul 14 0 8, .mul 15 1 9, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 8 9, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

/-! ## Constants -/

/-- The seven 64-bit words of `v`, lowest first. -/
def words7 (v : Nat) : List (BitVec 64) := (List.range 7).map fun i => BitVec.ofNat 64 (v >>> (64 * i))

/-- The field element `v` into slot `i`. -/
def constSlot (i : Nat) (v : Spec.X448.Fe) : List Instr :=
  (W.zip (words7 v.val)).map (fun (r, x) => .movImm64 r x) ++ stores (slot i) W

/-- `R` the neutral point `(0 : 1 : 1)`, `Q` the base point `(X : Y : 1)`, and
`d`. -/
def consts : List Instr :=
  constSlot 0 0 ++ constSlot 1 1 ++ constSlot 2 1 ++ constSlot 8 Spec.Ed448.basePoint.X ++
    constSlot 9 Spec.Ed448.basePoint.Y ++ constSlot 10 1 ++ constSlot 11 Spec.Ed448.d

/-! ## The scalar's bits -/

/-- The body of the loop over the scalar's 57 bytes (the counter `rbx`):
bit `j` of byte `rbx` at `BITS + 8 rbx + j`. -/
def bitsBody : List Instr :=
  [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1), .store8 (bitAt j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 57)]

def bits : Prog isa := .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (.block bitsBody) .ne)

/-! ## The loop over the bits -/

/-- `rcx = -BITS[rbx]`: the mask of bit `rbx`. -/
def bitMask : List Instr :=
  [.movzx8 .rdx { base := .rdi, index := some .rbx, disp := (BITS : Int) }, .mov32 .rcx (.imm 0),
    .alu .sub .rcx (.reg .rdx)]

/-- One bit `t = rbx - 1`, from the top: `R = 2R`, `T = R + B`, and `T`
swapped into `R` if bit `t` is set. -/
def step (F : Field) : List Instr :=
  [.alu .sub .rbx (.imm 1)] ++ fieldCode F doubleOps ++ fieldCode F addOps ++ bitMask ++
    cswap (slot 0) (slot 3) ++ cswap (slot 1) (slot 4) ++ cswap (slot 2) (slot 5) ++
    [.alu .test .rbx (.reg .rbx)]

/-- The 456 bits, from 455 down to 0. -/
def mulLoop (F : Field) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 456)]) (.loop (.block (step F)) .ne)

/-! ## Entry and exit -/

/-- The callee-saved registers saved at the working space `rdx`, the output's
address at `OUT`, the working space into `rdi`, and the constants. -/
def entry : List Instr :=
  saveAt .rdx ++ ([.store (at_ .rdx OUT) .rdi, .mov .rdi (.reg .rdx)] ++ consts)

/-- `x = X/Z` into slot 3 and `y = Y/Z` into slot 4, with `1/Z` in slot 21
(the inversion's result); `y` fully reduced to the output's first 56 bytes,
and the low bit of `x` as the top bit of its 57th; then the callee-saved
registers restored. -/
def encode (F : Field) : List Instr :=
  F.mul (slot 3) (slot 0) (slot 21) ++ (F.mul (slot 4) (slot 1) (slot 21) ++ (freeze (slot 4) ++
    ([.mov .rax (.mem (sc OUT))] ++ ((List.range 7).map (fun i => .store (at_ .rax (8 * i)) (w i)) ++
    (freeze (slot 3) ++ ([.mov .rax (.mem (sc OUT)), .alu .and .r8 (.imm 1), .shift .ror .r8 57,
      .store8 (at_ .rax 56) .r8] ++ Impl.X448.X86_64.restore))))))

/-- `vg_ed448_scalar_base` with the field multiplications `F`. -/
def scalarBaseWith (F : Field) : Prog isa :=
  .seq (.block entry) <| .seq bits <| .seq (mulLoop F) <| .seq (invert F) (.block (encode F))

def scalarBase : Prog isa := scalarBaseWith Impl.X448.X86_64.baseline

def scalarBaseAdx : Prog isa := scalarBaseWith Impl.X448.X86_64.adx

end VG.Impl.Ed448.X86_64
