import VerifiedGarbage.Impl.Ed25519.X86.Scalar

namespace VG.Impl.Ed25519.X86
open VG.X86 VG.Impl.X25519.X86

/-- The addend contributes only to the low eight columns. -/
def scalarMulTerms (k : Nat) : List Term :=
  prodTerms 256 288 k ++ if k < 8 then [.addM (320 + 4 * k)] else []

def scalarWideMul : List Instr := zeroAcc ++ cols 128 16 scalarMulTerms

def scalarMulInputs : List Instr :=
  ([.mov .esi (.mem (at_ .esp 12))] : List Instr) ++ copyWords 256 8 ++
  ([.mov .esi (.mem (at_ .esp 16))] : List Instr) ++ copyWords 288 8 ++
  ([.mov .esi (.mem (at_ .esp 8))] : List Instr) ++ copyWords 320 8

def scalarMulAdd : Prog isa :=
  .seq (.block (abiSave 4 ++ scalarMulInputs ++ scalarWideMul))
    (.seq scalarEngine (.block (finishWords scalarR)))
end VG.Impl.Ed25519.X86
