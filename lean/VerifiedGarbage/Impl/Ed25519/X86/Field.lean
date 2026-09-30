import VerifiedGarbage.Impl.X25519.X86
import VerifiedGarbage.Spec.Ed25519

/-! Extended Edwards formulas on the eight-word field representation.
Slots 0–21 occupy bytes 64–767 of the eight-KiB workspace. -/

namespace VG.Impl.Ed25519.X86
open VG.X86

abbrev Slot := Fin 22

def offset (s : Slot) : Nat := 64 + 32 * s.val

def constField (o : Slot) (v : Spec.X25519.Fe) : List Instr :=
  (List.range 8).flatMap fun k =>
    [.mov .eax (.imm (BitVec.ofNat 32 (v.val / (2 ^ 32) ^ k))),
      .store (VG.Impl.X25519.X86.sc (offset o + 4 * k)) .eax]

def copyField (o a : Slot) : List Instr := VG.Impl.X25519.X86.copy (offset o) (offset a)

/-- Small field programs, lowered to the existing verified integer code. -/
inductive FieldOp where
  | copy (out a : Slot)
  | const (out : Slot) (v : Spec.X25519.Fe)
  | mul (out a b : Slot)
  | add (out a b : Slot)
  | sub (out a b : Slot)
  deriving DecidableEq

def FieldOp.code : FieldOp → List Instr
  | .copy o a => copyField o a
  | .const o v => constField o v
  | .mul o a b => VG.Impl.X25519.X86.mul (offset o) (offset a) (offset b)
  | .add o a b => VG.Impl.X25519.X86.add (offset o) (offset a) (offset b)
  | .sub o a b => VG.Impl.X25519.X86.sub (offset o) (offset a) (offset b)

def fieldCode (ops : List FieldOp) : List Instr := ops.flatMap FieldOp.code

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

def pointAdd : List Instr := fieldCode pointAddOps

/-- Double the first point, using the complete addition formula on two
equal inputs. Uses precisely the same formula as the specification. -/
def pointDoubleOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 8,
  .add 9 1 0, .mul 9 9 9,
  .mul 10 3 16, .add 10 10 10, .mul 10 10 3,
  .add 11 2 2, .mul 11 11 2,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointDouble : List Instr := fieldCode pointDoubleOps

end VG.Impl.Ed25519.X86
