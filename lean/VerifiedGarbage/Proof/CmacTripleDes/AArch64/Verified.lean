import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Init
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Finalize
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.CT
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Implies
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# TDEA-CMAC on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time under this target's contracts (`Contract.lean`), and the shared
contracts of `Spec/Cmac/TripleDesContract.lean`, which imply them, with no
stack: the functions call nothing, and write only `x0`–`x17`.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.Impl.CmacTripleDes.AArch64

/-- The ABI's obligations, for code that writes none of the registers it
preserves and no vector register, and calls nothing. -/
theorem abi_of {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : c.allInstrs (fun i => preserved.all fun r => dstOf i != some r) = true)
    (hn : c.noCalls = true) (hv : c.allInstrs keepsV = true) :
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Q s' := by
  obtain ⟨t, s', he, hq, hg⟩ := WP.gprs h hc hn
  exact ⟨t, s', he, ⟨hg, Exec.sp he, Exec.preservedV he hv⟩, hq⟩

theorem init_correct (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  abi_of (init_wp hs) (by lit_decide) (by lit_decide) (by lit_decide)

theorem update_correct (s : State) (hs : updateAArch64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s' :=
  abi_of (update_wp hs) (by lit_decide) (by lit_decide) (by lit_decide)

theorem finalize_correct (s : State) (hs : finalizeAArch64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeAArch64.post s s' :=
  abi_of (finalize_wp hs) (by lit_decide) (by lit_decide) (by lit_decide)

theorem init_verified : Verified AArch64.target init (Spec.Cmac.tdesInitContract AArch64.abi 0) :=
  Verified.of_correct init_correct init_ct init_implies

theorem update_verified : Verified AArch64.target update (Spec.Cmac.tdesUpdateContract AArch64.abi 0) :=
  Verified.of_correct update_correct update_ct update_implies

theorem finalize_verified : Verified AArch64.target finalize (Spec.Cmac.tdesFinalizeContract AArch64.abi 0) :=
  Verified.of_correct finalize_correct finalize_ct finalize_implies

end VG.Proof.CmacTripleDes.AArch64
