import VerifiedGarbage.Proof.CmacTripleDes.X86.FinalizeCorrect
import VerifiedGarbage.Proof.CmacTripleDes.X86.CT
import VerifiedGarbage.Proof.CmacTripleDes.X86.Implies

/-!
# TDEA-CMAC on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time under this target's contracts (`Contract.lean`), and the shared
contracts of `Spec/Cmac/TripleDesContract.lean`, which imply them, with no
stack: the functions call nothing, and save our caller's registers in the
scratch buffer.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86

theorem init_verified : Verified X86.target init (Spec.Cmac.tdesInitContract X86.abi 0) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct init_implies

theorem update_verified : Verified X86.target update (Spec.Cmac.tdesUpdateContract X86.abi 0) :=
  Verified.of_correct (fun _ hs => update_wp hs) update_ct update_implies

theorem finalize_verified : Verified X86.target finalize (Spec.Cmac.tdesFinalizeContract X86.abi 0) :=
  Verified.of_correct (fun _ hs => finalize_wp hs) finalize_ct finalize_implies

end VG.Proof.CmacTripleDes.X86
