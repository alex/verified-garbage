import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# The polynomial arithmetic a top-level function of ML-KEM calls on x86-64

What the top-level functions need of the implementations of
`vg_mlkem_multiply_ntts`, `vg_mlkem_ntt` and `vg_mlkem_inv_ntt` they call
(`Impl.MlKem.X86_64.Arith`): each meets its contract, is constant time, never
writes the stack pointer, makes no calls, and keeps MXCSR's control bits
(`ArithOk`). Both `Arith.sse` and `Arith.avx2` do (`ArithOk.sse`,
`ArithOk.avx2`); the top-level functions call the one that goes with their
implementation of `vg_mlkem_sample_ntt4` (`Callee4.arith`,
`Sample4Impl.arith`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

/-- What a caller needs of a function with the contract `k`. -/
structure CalleeOk (k : Contract isa) (c : Prog isa) : Prop where
  ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  nosp : NoSp c
  depth : c.depth = 0
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true

/-- The polynomial arithmetic `A` is correct, constant time, and safe to call. -/
structure ArithOk (A : Arith) : Prop where
  mul : CalleeOk mulK A.mul
  ntt : CalleeOk (inPlaceK ntt) A.ntt
  nttInv : CalleeOk (inPlaceK nttInv) A.nttInv

theorem ArithOk.sse : ArithOk .sse where
  mul := ⟨mul_correct, mul_ct, nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩
  ntt := ⟨ntt_correct, ntt_ct, nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩
  nttInv := ⟨nttInv_correct, nttInv_ct, nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩

theorem ArithOk.avx2 : ArithOk .avx2 where
  mul := ⟨mulY_correct, mulY_ct, nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩
  ntt := ⟨nttY_correct, nttY_ct, nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩
  nttInv := ⟨nttInvY_correct, nttInvY_ct, nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩

end VG.Proof.MlKem.X86_64
