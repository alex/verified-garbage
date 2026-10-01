import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Backend
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt

/-!
# ML-DSA on x86-64: what the callers of the polynomial arithmetic need of it

Untrusted: everything here is checked by Lean. An `ArithImpl` is an
implementation of the polynomial arithmetic (`Impl.MlDsa.X86_64.Arith.Backend`)
with what key generation, signing and verification need of each of its
functions (`FnOk`): it meets its contract without using the stack, never
writes `rsp`, calls no deeper than twice, and loads MXCSR only to restore
it. Each is a variant of the interface `MlDsaArith` on x86-64
(`Variants/MlDsaArith/X86_64/`), and the functions that call it are proven
once for all of them (`Generic/MlDsaArith/X86_64/`).
-/

namespace VG.Proof.MlDsa.X86_64

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith

/-- What a caller needs of a function with the contract `k` (given the
stack its calls use) and the code `c`. -/
structure FnOk (k : Nat → Contract isa) (c : Prog isa) : Prop where
  ver : Verified X86_64.target c (k 0)
  nosp : NoSp c
  depth : c.depth ≤ 2
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true

/-- Each function of the backend `B` meets its contract, and is safe to call. -/
structure BackendOk (B : Backend) : Prop where
  ntt : FnOk (fun S => Spec.MlDsa.nttContract X86_64.abi S) B.ntt
  invNtt : FnOk (fun S => Spec.MlDsa.nttInvContract X86_64.abi S) B.invNtt
  mul : FnOk (fun S => Spec.MlDsa.mulContract X86_64.abi S) B.mul
  mulAdd : FnOk (fun S => Spec.MlDsa.mulAddContract X86_64.abi S) B.mulAdd
  add : FnOk (fun S => Spec.MlDsa.addContract X86_64.abi S) B.add
  sub : FnOk (fun S => Spec.MlDsa.subContract X86_64.abi S) B.sub
  highBits : FnOk (fun S => Spec.MlDsa.highBitsContract X86_64.abi S) B.highBits
  lowBits : FnOk (fun S => Spec.MlDsa.lowBitsContract X86_64.abi S) B.lowBits
  normLt : FnOk (fun S => Spec.MlDsa.normLtContract X86_64.abi S) B.normLt
  makeHint : FnOk (fun S => Spec.MlDsa.makeHintContract X86_64.abi S) B.makeHint
  useHint : FnOk (fun S => Spec.MlDsa.useHintContract X86_64.abi S) B.useHint

/-- An implementation of the polynomial arithmetic on x86-64. -/
structure ArithImpl where
  code : Backend
  ok : BackendOk code
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

/-- `FnOk` of code verified without stack, from evaluating it. -/
theorem FnOk.of {k : Nat → Contract isa} {c : Prog isa} (h : Verified X86_64.target c (k 0))
    (hn : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) (hd : c.depth ≤ 2) (hc : ctlOk c = true)
    (hs : c.allInstrs (fun i => !isa.writesSp i) = true) : FnOk k c :=
  ⟨h, Proof.MlKem.X86_64.nosp_of hn, hd, hc, Code.all_of_allInstrs hs⟩

/-- The SSE2 code. -/
def ArithImpl.sse2 : ArithImpl where
  code := .sse2
  ok :=
    { ntt := FnOk.of Arith.ntt_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      invNtt := FnOk.of Arith.nttInv_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      mul := FnOk.of Arith.mul_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      mulAdd := FnOk.of Arith.mulAdd_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      add := FnOk.of Arith.add_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      sub := FnOk.of Arith.sub_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      highBits := FnOk.of Round.highBits_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      lowBits := FnOk.of Round.lowBits_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      normLt := FnOk.of Round.normLt_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      makeHint := FnOk.of Round.makeHint_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      useHint := FnOk.of Round.useHint_verified (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) }
  features := []

end VG.Proof.MlDsa.X86_64
