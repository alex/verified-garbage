import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
import VerifiedGarbage.Impl.MlKem1024.X86.Kem
import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.TCB.X86.Target

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_check_ek`

The key check (`Proof/MlKem/X86/CheckEkBody.lean`) of ML-KEM-1024: its 512
groups of `ek[0 : 1536]`.
-/

namespace VG.Proof.MlKem1024.X86.CheckEk

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.CheckEk
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem Pre.of {s₀ : State} (h : (Spec.MlKem1024.checkEkContract X86.abi 16).pre s₀) : Pre mlKem1024 s₀ := by
  sig_pre [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- All-zero memory. -/
def satMem : Mem := fun _ => 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.checkEk (Spec.MlKem1024.checkEkContract X86.abi 16) := by
  refine Piece.verified (((piece (p := mlKem1024) (by decide) (NoSp.of_all (by decide +kernel))).pre_mono
    (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, -, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hinv.eax]
    by_cases e : ok (K mlKem1024 s₀) (128 * mlKem1024.k)
    · rw [ite_eq_left e]; exact (ite_eq_left (ok_iff.mpr e)).symm
    · rw [ite_eq_right e]; exact (ite_eq_right fun h => e (ok_iff.mp h)).symm
  · let st := satState satMem [⟨0, 1568⟩, ⟨0x5004, 4⟩] []
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlKem1024.X86.CheckEk
