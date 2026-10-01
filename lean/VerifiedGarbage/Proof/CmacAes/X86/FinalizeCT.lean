import VerifiedGarbage.Proof.CmacAes.X86.FinalizeCorrect
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT

/-!
# AES-CMAC on x86: `vg_cmac_aes_finalize` is constant time

Untrusted: everything here is checked by Lean. The code before the call is
checked by the taint analysis, from `esp` and the stack arguments (its
branches and the copy loop depend only on `last_len`), the call of
`vg_aes_ctr32`, in its frame, is constant time by its own proof
(`ctr_rel`), its arguments pinned by the correctness proof (`FMid`), and the
restore after it by the taint analysis again.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86

theorem FPre.argsOut {s₀ : State} (hp : FPre s₀) {s : State} (hesp : s.gpr .esp = E s₀) (hwr : s.wr = s₀.wr) :
    ArgsOut 6 s := by
  have hs : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.args_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.args_scr

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem fagree {s₀ s₀' : State} (hq : finalizeX86.pub s₀ s₀') (hp : FPre s₀) (hp' : FPre s₀') {rs : List Reg}
    {s₁ s₂ : State} (h₁ : Pt s₀ s₁) (h₂ : Pt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp]; exact hq.1) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by rw [arg_cur (h₁.esp) (h₁.args i hi), arg_cur (h₂.esp) (h₂.args i hi), hq.2 i hi]

theorem FMid.f {s₀ s : State} (h : FMid s₀ s) :
    Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem :=
  h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩

theorem FMid.pt {s₀ : State} (hp : FPre s₀) {s : State} (h : FMid s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (UPre.big_of h.f) hi⟩

theorem fcall_after {s₀ : State} (hp : FPre s₀) {s : State} (h : FMid s₀ s) : WP isa ctrCall s (Pt s₀) :=
  WP.mono (ctr_call h.pre) fun s' hc => by
    have hb : below (s.gpr .esp) 28 = stkR s₀ := by rw [h.esp]; exact hp.below_eq
    have fr := hc.frame
    rw [hb, hp.cA] at fr
    have big := UPre.big_of (h.f.trans (fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩))
    exact ⟨by rw [hc.saved .esp (by simp [calleeSaved]), h.esp], by rw [hc.wr, h.wr],
      fun _ hi => hp.arg_keep big hi⟩

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizeX86.pre s₀) (h0' : finalizeX86.pre s₀')
    (hq : finalizeX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finalize fun _ _ => True := by
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  have eW : W s₀ = W s₀' := hq.2 0 (by decide)
  have eR : R s₀ = R s₀' := by rw [R, R, hq.2 1 (by decide)]
  have eSt : St s₀ = St s₀' := hq.2 2 (by decide)
  have eS : S s₀ = S s₀' := hq.2 5 (by decide)
  have pt₀ : ∀ {t : State}, Pt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact fagree hq hp hp' pt₀ pt₀ fun r hr => by simp at hr)
    (c := finPre) (by taint_decide)).wp (F₁ := FMid s₀) (F₂ := FMid s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c := ((ctr_rel (E := E s₀) (P := fun s₁ s₂ => FMid s₀ s₁ ∧ FMid s₀' s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [eW, eS, eSt, eR]; exact h.2.pre, h.1.esp, h.2.esp.trans hq.1.symm⟩).wp
      (F₁ := Pt s₀) (F₂ := Pt s₀') fun _ _ h => ⟨fcall_after hp h.1, fcall_after hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => Pt s₀ s₁ ∧ Pt s₀' s₂) (argTaint [] (4 + 4 * 6))
    (fun _ _ h => fagree hq hp hp' h.1 h.2 fun r hr => by simp at hr)
    (c := .block (restore 5)) (by taint_decide)
  exact a.seq (c.seq b)

theorem finalize_ct : ConstantTime isa finalizeX86.pre finalizeX86.pub finalize :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86
