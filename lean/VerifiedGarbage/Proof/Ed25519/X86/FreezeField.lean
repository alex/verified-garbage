import VerifiedGarbage.Proof.Ed25519.X86.Field

/-! Canonical reduction preserves the field environment. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (freeze T)
open VG.Proof.X25519 (toFe toFe_mod)

theorem freezeField_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (a : Slot) :
    WP isa (.block (freeze (offset a))) s fun t => FieldKeep x s t ∧
      env t.mem x = env s.mem x ∧ fe t.mem x (offset a) = (env s.mem x a).val := by
  refine WP.mono (freeze_ok hc (slot_valid a)) fun t ⟨hk, hf, hv⟩ => ?_
  have fit := hc.fit
  refine ⟨⟨hk, frame_wide hc.fit4 (slot_valid a) (by decide) hf⟩, ?_, hv⟩
  funext i
  by_cases hi : i = a
  · subst i
    change toFe (fe t.mem x (offset a)) = _
    rw [hv]; exact toFe_mod _
  · apply congrArg toFe
    apply fe_frame
    intro k hk'
    apply wd_frame hf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hs := slot_ne (slot_valid a) (slot_valid i) (fun h => hi (offset_inj h))
      exact sub_disj (by simp only [offset]; omega_using [fit, i.isLt, hk'])
        (by simp only [offset]; omega_using [fit, a.isLt]) (by omega_using [hs, hk'])
    · exact sub_disj (by simp only [offset]; omega_using [fit, i.isLt, hk'])
        (by simp only [T]; omega_using [fit]) (Or.inl (by simp only [offset, T]; omega))

end VG.Proof.Ed25519.X86
