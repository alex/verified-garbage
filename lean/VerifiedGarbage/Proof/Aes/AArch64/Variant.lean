import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
import VerifiedGarbage.Impl.Aes.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# Implementations of `vg_aes_ctr32` on AArch64

A `Ctr32Impl` is what a function that calls `vg_aes_ctr32` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `AesCtr32` on AArch64 (`Variants/AesCtr32/AArch64/`), and each
caller (in `Generic/AesCtr32/AArch64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Every implementation is proven against the same contract,
`Proof.Aes.ctr32AArch64`, and has no frames. It comes with the
implementation of `vg_aes_expand_key` that goes with it (with the same
suffix and CPU features), for the callers that also expand the key, proven
against `Proof.Aes.expandKeyAArch64`.
-/

namespace VG.Proof.Aes.AArch64

open VG.AArch64

/-- An implementation of `vg_aes_ctr32` on AArch64. -/
structure Ctr32Impl where
  /-- Its symbol and code. -/
  callee : Impl.Aes.AArch64.Ctr32
  /-- It has no frames (`WP.call`). -/
  noFrames : callee.code.noFrames = true
  ok : ∀ s, Proof.Aes.ctr32AArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32AArch64.post s s'
  ct : ConstantTime isa Proof.Aes.ctr32AArch64.pre Proof.Aes.ctr32AArch64.pub callee.code
  /-- It never writes v8–v15. -/
  keepsV : callee.code.allInstrs keepsV = true
  /-- What the names of its callers' instances end with (e.g. `_aes`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.AArch64.ExpandKey
  expandNoFrames : expand.code.noFrames = true
  expandOk : ∀ s, Proof.Aes.expandKeyAArch64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyAArch64.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyAArch64.pre Proof.Aes.expandKeyAArch64.pub expand.code
  expandKeepsV : expand.code.allInstrs AArch64.keepsV = true

namespace Ctr32Impl

/-- The bitsliced implementation, `vg_aes_ctr32`, in the baseline ISA. -/
def scalar : Ctr32Impl where
  callee := .scalar
  noFrames := by decide +kernel
  ok := ctr32_correct
  ct := ctr32_ct
  keepsV := by decide +kernel
  suffix := ""
  features := []
  expand := .scalar
  expandNoFrames := by decide +kernel
  expandOk := expandKey_correct
  expandCt := expandKey_ct
  expandKeepsV := by decide +kernel

/-- The implementation with the Cryptographic Extension, `vg_aes_ctr32_aes`. -/
def aese : Ctr32Impl where
  callee := .aese
  noFrames := by decide +kernel
  ok := Aese.ctr32_correct
  ct := Aese.ctr32_ct
  keepsV := by decide +kernel
  suffix := "_aes"
  features := ["aes"]
  expand := .aese
  expandNoFrames := by decide +kernel
  expandOk := Aese.Key.expandKey_correct
  expandCt := Aese.Key.expandKey_ct
  expandKeepsV := by decide +kernel

end Ctr32Impl

end VG.Proof.Aes.AArch64
