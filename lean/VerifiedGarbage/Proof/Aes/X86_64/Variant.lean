import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Impl.Aes.X86_64.Callee
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# Implementations of `vg_aes_ctr32` on x86-64

Untrusted: everything here is checked by Lean.

A `Ctr32Impl` is what a function that calls `vg_aes_ctr32` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `AesCtr32` on x86-64 (`Variants/AesCtr32/X86_64/`), and each caller
(in `Generic/AesCtr32/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Every implementation is proven against the same contract,
`Proof.Aes.ctr32X86_64`, and makes no calls. It comes with the
implementation of `vg_aes_expand_key` that goes with it (with the same
suffix and CPU features), for the callers that also expand the key, proven
against `Proof.Aes.expandKeyX86_64`.
-/

namespace VG.Proof.Aes.X86_64

open VG.X86_64

/-- An implementation of `vg_aes_ctr32` on x86-64. -/
structure Ctr32Impl where
  /-- Its symbol and code. -/
  callee : Impl.Aes.X86_64.Ctr32
  /-- It makes no calls. -/
  depth : callee.code.depth = 0
  ok : ∀ s, Proof.Aes.ctr32X86_64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32X86_64.post s s'
  ct : ConstantTime isa Proof.Aes.ctr32X86_64.pre Proof.Aes.ctr32X86_64.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_aesni`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.X86_64.ExpandKey
  expandDepth : expand.code.depth = 0
  expandOk : ∀ s, Proof.Aes.expandKeyX86_64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86_64.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub expand.code
  expandNosp : NoSp expand.code
  expandMxcsr : expand.code.allInstrs (fun i => !loadsMxcsr i) = true
  expandSpSafe : expand.code.all (fun i => !isa.writesSp i) = true

namespace Ctr32Impl

theorem scalar_nosp : NoSp Impl.Aes.X86_64.Ctr32.scalar.code := by
  have : ((instrs Impl.Aes.X86_64.Ctr32.scalar.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

theorem expandKey_nosp : NoSp Impl.Aes.X86_64.ExpandKey.scalar.code := by
  have : ((instrs Impl.Aes.X86_64.ExpandKey.scalar.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- The bitsliced implementation, `vg_aes_ctr32`, in the baseline ISA. -/
def scalar : Ctr32Impl where
  callee := .scalar
  depth := by lit_decide
  ok := ctr32_correct
  ct := ctr32_ct
  nosp := scalar_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []
  expand := .scalar
  expandDepth := by lit_decide
  expandOk := expandKey_correct
  expandCt := expandKey_ct
  expandNosp := expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)

theorem aesni_nosp : NoSp Impl.Aes.X86_64.Ctr32.aesni.code := by
  have : ((instrs Impl.Aes.X86_64.Ctr32.aesni.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- `vg_aes_ctr32_aesni`'s own contract is the same, but for `rsp`, which its
public data leaves out. -/
theorem aesni_ct : ConstantTime isa Proof.Aes.ctr32X86_64.pre Proof.Aes.ctr32X86_64.pub
    Impl.Aes.X86_64.Ctr32.aesni.code :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨a, b, c, d, e, f, _⟩ e₁ e₂ =>
    AesNi.ctr32_ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨a, b, c, d, e, f⟩ e₁ e₂

theorem aesni_expandKey_nosp : NoSp Impl.Aes.X86_64.ExpandKey.aesni.code := by
  have : ((instrs Impl.Aes.X86_64.ExpandKey.aesni.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- `vg_aes_expand_key_aesni`'s own contract asks less of its arguments. -/
theorem aesni_expandKey_ok : ∀ s, Proof.Aes.expandKeyX86_64.pre s →
    ∃ t s', Exec isa Impl.Aes.X86_64.ExpandKey.aesni.code s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyX86_64.post s s' :=
  fun s ⟨a, b, _, _, _, c, _, d⟩ => AesNi.Key.expandKey_correct s ⟨a, b, c, d⟩

/-- … and its public data leave out `rsp`. -/
theorem aesni_expandKey_ct : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub
    Impl.Aes.X86_64.ExpandKey.aesni.code :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, b, _, _, _, c, _, d⟩ ⟨a', b', _, _, _, c', _, d'⟩ ⟨e, f, g, h, _⟩ e₁ e₂ =>
    AesNi.Key.expandKey_ct s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ ⟨e, f, g, h⟩ e₁ e₂

/-- The AES-NI implementation, `vg_aes_ctr32_aesni`. -/
def aesni : Ctr32Impl where
  callee := .aesni
  depth := by lit_decide
  ok := AesNi.ctr32_correct
  ct := aesni_ct
  nosp := aesni_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_aesni"
  features := ["aes", "ssse3"]
  expand := .aesni
  expandDepth := by lit_decide
  expandOk := aesni_expandKey_ok
  expandCt := aesni_expandKey_ct
  expandNosp := aesni_expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)

end Ctr32Impl

end VG.Proof.Aes.X86_64
