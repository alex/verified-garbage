import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Init
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.FinalizeCorrect
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.CT
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Implies
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# TDEA-CMAC on x86-64: `Verified`

Correctness and constant time under this target's contracts (`Contract.lean`),
and the shared contracts of `Spec/Cmac/TripleDesContract.lean`, which imply
them, with no stack: the functions call nothing.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.X86_64

theorem init_mx : init.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem update_mx : update.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem finalize_mx : finalize.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem init_correct (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec init_mx he hg, hp⟩

theorem update_correct (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := update_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec update_mx he hg, hp⟩

theorem finalize_correct (s : State) (hs : finalizeX86_64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalize_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec finalize_mx he hg, hp⟩

theorem init_verified : Verified X86_64.target init (Spec.Cmac.tdesInitContract X86_64.abi 0) :=
  Verified.of_correct init_correct init_ct init_implies

theorem update_verified : Verified X86_64.target update (Spec.Cmac.tdesUpdateContract X86_64.abi 0) :=
  Verified.of_correct update_correct update_ct update_implies

theorem finalize_verified : Verified X86_64.target finalize (Spec.Cmac.tdesFinalizeContract X86_64.abi 0) :=
  Verified.of_correct finalize_correct finalize_ct finalize_implies

end VG.Proof.CmacTripleDes.X86_64
