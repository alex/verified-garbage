import VerifiedGarbage.Proof.MlKem.Arm.DecapsCT
import VerifiedGarbage.Proof.MlKem1024.Arm.Calls

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_decaps`, `Verified`

The decapsulation of `Proof/MlKem/Arm/DecapsCT.lean` for `kl1024`: its precondition
from the contract's, and the contract's postcondition from what it shows.
-/

namespace VG.Proof.MlKem1024.Arm.Decaps

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm VG.Proof.MlKem1024.Arm
open VG.Proof.MlKem.Arm.Enc
open VG.Proof.MlKem.Arm.Decaps hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Spec.MlKem1024.decapsContract Arm.abi 8).pre s) : Pre kl1024 s := by
  sig_pre [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, h1, h2, h3, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if okEnc kl1024.k (ρD kl1024 s₀) kl1024.k then 1 else 0)
    (hkey : bytesAt s.mem (State.addr (pKey s₀)) 32 =
      if CT kl1024 s₀ = C2 kl1024 s₀ then K1 kl1024 s₀ else KB kl1024 s₀) :
    (Spec.MlKem1024.decapsContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  have e0 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 3168 = DK kl1024 s₀ := (DK_eq kl1024 s₀).symm
  have e1 : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 1568 = CT kl1024 s₀ := (CT_eq kl1024 s₀).symm
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 32 =
      if CT kl1024 s₀ = C2 kl1024 s₀ then K1 kl1024 s₀ else KB kl1024 s₀ := hkey
  rw [setWidth_append32, h0, e0, e1, e2]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x10000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified Arm.target Impl.MlKem1024.Arm.decaps1024 (Spec.MlKem1024.decapsContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hkey⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, post_of h0 hkey⟩
  · sig_pub [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    have hr : ρD kl1024 s₁ = ρD kl1024 s₂ := by
      rw [ρD_eq, ρD_eq, DK_eq, DK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem1024.Arm.Decaps
