import VerifiedGarbage.Proof.Rc4.AArch64.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.ApplyCT
import VerifiedGarbage.Proof.Rc4.AArch64.Apply
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc4.Contract

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4

def applySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 1 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩, ⟨0x3000, 64⟩]

theorem apply_verified : Verified AArch64.target VG.Impl.Rc4.AArch64.apply
    (Spec.Rc4.applyContract AArch64.abi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    sig_pre [Spec.Rc4.applyContract, Spec.Rc4.applySig, AArch64.abi, AArch64.argRegs] at hs
    obtain ⟨_, hwr, hsep, _⟩ := hs
    have hp : InRegions s.wr (s.gpr .x0) 258 := by
      refine ⟨⟨s.gpr .x0, 258⟩, ?_, ?_⟩
      · rw [hwr]; exact List.mem_cons_self
      · simp only [Region.Contains, BitVec.sub_self]; decide
    have hd : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region) ∈ s.wr := by
      rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have hsep' : Mem.Sep (s.gpr .x0) 258 (s.gpr .x1) (s.gpr .x2).toNat :=
      hsep.sep (by simp [Region.Contains]) (by simp [Region.Contains])
    obtain ⟨tr, t, he, hpost, hregs⟩ := WP.gprs (rs := preserved) (apply_ok s hp hd hsep')
      (by lit_decide) (by rfl)
    refine ⟨tr, t, he, ⟨hregs, Exec.sp he, hpost.2⟩, ?_⟩
    sig_post [Spec.Rc4.applyContract, Spec.Rc4.applySig, AArch64.abi, AArch64.argRegs]
    exact hpost.1
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ hpre₁ hpre₂ hpub he₁ he₂
    sig_pre [Spec.Rc4.applyContract, Spec.Rc4.applySig, AArch64.abi, AArch64.argRegs] at hpre₁ hpre₂
    sig_pub [Spec.Rc4.applyContract, Spec.Rc4.applySig, AArch64.abi, AArch64.argRegs] at hpub
    obtain ⟨hsp, hleak, h0, h1, h2, _⟩ := hpub
    have hp₁ : ReadValid s₁ := by
      refine ⟨⟨s₁.gpr .x0, 258⟩, List.mem_append_right _ ?_, ?_⟩
      · rw [hpre₁.2.1]; exact List.mem_cons_self
      · simp only [Region.Contains, BitVec.sub_self]; decide
    have hp₂ : ReadValid s₂ := by
      refine ⟨⟨s₂.gpr .x0, 258⟩, List.mem_append_right _ ?_, ?_⟩
      · rw [hpre₂.2.1]; exact List.mem_cons_self
      · simp only [Region.Contains, BitVec.sub_self]; decide
    have hi : (contextAt s₁.mem (s₁.gpr .x0)).i = (contextAt s₂.mem (s₂.gpr .x0)).i :=
      BitVec.eq_of_toNat_eq (List.cons.inj hleak).1
    exact apply_ct s₁ s₂ tr₁ tr₂ t₁ t₂ hp₁ hp₂ ⟨hsp, h0, h1, h2, hi⟩ he₁ he₂
  · sig_implies_sat [Spec.Rc4.applyContract, Spec.Rc4.applySig, AArch64.abi, AArch64.argRegs]
      [applySat] using applySat

end VG.Proof.Rc4.AArch64
