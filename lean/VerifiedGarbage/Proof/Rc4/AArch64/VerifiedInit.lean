import VerifiedGarbage.Proof.Rc4.AArch64.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Init
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Rc4.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc4.Contract

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩, ⟨0x3000, 64⟩]

theorem init_verified : Verified AArch64.target VG.Impl.Rc4.AArch64.init
    (Spec.Rc4.initContract AArch64.abi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    sig_pre [Spec.Rc4.initContract, Spec.Rc4.initSig, AArch64.abi, AArch64.argRegs] at hs
    obtain ⟨hrd, hwr, _, _⟩ := hs
    have hp : InRegions s.wr (s.gpr .x2) 258 := by
      refine ⟨⟨s.gpr .x2, 258⟩, ?_, ?_⟩
      · rw [hwr]; exact List.mem_cons_self
      · simp only [Region.Contains, BitVec.sub_self]; decide
    have hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat := by
      refine ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ?_, ?_⟩
      · rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _)
      · simp [Region.Contains]
    have hw := WP.gprs (rs := preserved) (init_ok s hp hk) (by lit_decide) (by rfl)
    obtain ⟨tr, t, he, ⟨hpost, hv⟩, hregs⟩ := hw
    refine ⟨tr, t, he, ⟨hregs, Exec.sp he, hv⟩, ?_⟩
    sig_post [Spec.Rc4.initContract, Spec.Rc4.initSig, AArch64.abi, AArch64.argRegs]
    cases hc : Spec.Rc4.init (Spec.Rc4.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
    | ok ctx =>
      rw [hc] at hpost
      dsimp only at hpost ⊢
      exact ⟨by rw [hpost.1]; rfl, hpost.2⟩
    | error err =>
      cases err
      rw [hc] at hpost
      dsimp only at hpost ⊢
      rw [hpost]
      rfl
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hpub he₁ he₂
    sig_pub [Spec.Rc4.initContract, Spec.Rc4.initSig, AArch64.abi, AArch64.argRegs] at hpub
    obtain ⟨hsp, h0, h1, h2, h3⟩ := hpub
    have hagree : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
      refine ⟨hsp, fun r hr => ?_⟩
      simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
    exact init_ct s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hagree he₁ he₂
  · sig_implies_sat [Spec.Rc4.initContract, Spec.Rc4.initSig, AArch64.abi, AArch64.argRegs]
      [initSat] using initSat

end VG.Proof.Rc4.AArch64
