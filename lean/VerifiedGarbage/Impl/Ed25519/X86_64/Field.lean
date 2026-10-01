import VerifiedGarbage.Impl.X25519.X86_64
import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519 field operations on x86-64

Field elements reuse X25519's four-word representation and arithmetic.
Slots 2 through 23 occupy bytes [64, 768) of the scratch buffer; the
first 64 bytes are reserved for saved registers and pointers.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (loads store4)

abbrev Slot := Fin 22

/-- The field multiplications the code is emitted with (X25519's): the baseline's, or BMI2
and ADX's. -/
abbrev Arith := VG.Impl.X25519.X86_64.Field

def offset (s : Slot) : Nat := 64 + 32 * s.val

def constWords (v : Spec.X25519.Fe) : List Instr :=
  [.movImm64 .r8 (BitVec.ofNat 64 v.val),
    .movImm64 .r9 (BitVec.ofNat 64 (v.val / 2 ^ 64)),
    .movImm64 .r10 (BitVec.ofNat 64 (v.val / 2 ^ 128)),
    .movImm64 .r11 (BitVec.ofNat 64 (v.val / 2 ^ 192))]

def constField (o : Slot) (v : Spec.X25519.Fe) : List Instr := constWords v ++ store4 (offset o)

def copyField (o a : Slot) : List Instr :=
  loads (offset a) .r8 .r9 .r10 .r11 ++ store4 (offset o)

/-- Small field programs, lowered to the existing verified integer code. -/
inductive FieldOp where
  | copy (out a : Slot)
  | const (out : Slot) (v : Spec.X25519.Fe)
  | mul (out a b : Slot)
  | sqr (out a : Slot)
  | add (out a b : Slot)
  | sub (out a b : Slot)
  deriving DecidableEq

def FieldOp.code (fld : Arith) : FieldOp → List Instr
  | .copy o a => copyField o a
  | .const o v => constField o v
  | .mul o a b => fld.mul (offset o) (offset a) (offset b)
  | .sqr o a => fld.sqr (offset o) (offset a)
  | .add o a b => Impl.X25519.X86_64.add (offset o) (offset a) (offset b)
  | .sub o a b => Impl.X25519.X86_64.sub (offset o) (offset a) (offset b)

def fieldCode (fld : Arith) (ops : List FieldOp) : List Instr := ops.flatMap (FieldOp.code fld)

/-- Add the points in slots 0–3 and 4–7 into slots 0–3. The coordinates
are X,Y,Z,T. Slot 16 holds d; slots 8–15 are temporary. Both points are
read before the result overwrites the first. -/
def pointAddOps : List FieldOp := [
  .sub 8 1 0, .sub 9 5 4, .mul 8 8 9,
  .add 9 1 0, .add 10 5 4, .mul 9 9 10,
  .mul 10 3 16, .add 10 10 10, .mul 10 10 7,
  .add 11 2 2, .mul 11 11 6,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointAdd (fld : Arith) : List Instr := fieldCode fld pointAddOps

/-- Double the first point, using the complete addition formula on two
equal inputs. Uses precisely the same formula as the specification. -/
def pointDoubleOps : List FieldOp := [
  .sub 8 1 0, .sqr 8 8,
  .add 9 1 0, .sqr 9 9,
  .mul 10 3 16, .add 10 10 10, .mul 10 10 3,
  .add 11 2 2, .mul 11 11 2,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointDouble (fld : Arith) : List Instr := fieldCode fld pointDoubleOps

end VG.Impl.Ed25519.X86_64
