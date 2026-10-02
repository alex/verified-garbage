import VerifiedGarbage.Proof.MlKem.Arm.EncapsCT
import VerifiedGarbage.Proof.MlKem1024.Arm.Calls

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_encaps`, `Verified`

The encapsulation of `Proof/MlKem/Arm/EncapsCT.lean` for `kl1024`: its precondition
from the contract's, and the contract's postcondition from what it shows.
-/

namespace VG.Proof.MlKem1024.Arm.Encaps

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm VG.Proof.MlKem1024.Arm
open VG.Proof.MlKem.Arm.Enc
open VG.Proof.MlKem.Arm.Encaps hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Spec.MlKem1024.encapsContract Arm.abi 8).pre s) : Pre kl1024 s := by
  sig_pre [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, b1, b2, b3, b4, b5, b6,
    f1, f2, f3, f4, f5⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, h1, h2, h3, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, b1, b2, b3,
    b4, b5, b6, f1, f2, f3, f4, f5⟩

theorem post_of {s₀ s : State}
    (h0 : s.gpr .r0 = if okEnc kl1024.k (ekRho kl1024.p (EK kl1024 s₀)) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey s₀)) 32 = KK kl1024 s₀)
    (hct : bytesAt s.mem (State.addr (pCt s₀)) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 s₀)) (RR kl1024 s₀)) (EK kl1024 s₀) (M kl1024 s₀) (RR kl1024 s₀)) :
    (Spec.MlKem1024.encapsContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e0 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 1568 = EK kl1024 s₀ := (EK_eq kl1024 s₀).symm
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 = KK kl1024 s₀ := hkey
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r3)) 1568 = VG.Proof.MlKem.KPke.ct kl1024.p
      (aEnc (ekRho kl1024.p (EK kl1024 s₀)) (RR kl1024 s₀)) (EK kl1024 s₀) (M kl1024 s₀) (RR kl1024 s₀) := hct
  rw [e0, ← M_eq, e1, e2]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0 else if a = 0x8001 then 0 else if a = 0x8002 then 1 else 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified Arm.target Impl.MlKem1024.Arm.encaps1024 (Spec.MlKem1024.encapsContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey, hct⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, post_of h0 hkey hct⟩
  · sig_pub [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, hs⟩ := hpub
    have hr : ekRho kl1024.p (EK kl1024 s₁) = ekRho kl1024.p (EK kl1024 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hs, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem1024.Arm.Encaps
