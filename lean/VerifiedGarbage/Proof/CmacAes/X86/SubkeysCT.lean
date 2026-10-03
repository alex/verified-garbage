import VerifiedGarbage.Proof.CmacAes.X86.Subkeys
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT

/-!
# AES-CMAC on x86: `vg_cmac_aes_subkeys` is constant time

The code before the call is checked by the taint analysis from `esp` and the
stack arguments (which nothing writes, `argTaint`), the call of
`vg_aes_ctr32`, in its frame, is constant time by its own proof (`ctr_rel`),
and the code after it by the taint analysis again, from `esp`, the stack
arguments and `ebx` (the subkeys, which the correctness proof pins).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)

theorem SPre.argsOut {s₀ : State} (hp : SPre s₀) {s : State} (hesp : s.gpr .esp = E s₀) (hwr : s.wr = s₀.wr) :
    ArgsOut 4 s := by
  have hs : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_k hp.args_k
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.args_scr

/-- What two runs agree on at a point between the calls. -/
structure SPt (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = E s₀
  wr : s.wr = s₀.wr
  args : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

section
variable {s₀ s₀' : State} (hq : subkeysX86.pub s₀ s₀')
include hq

theorem spub_arg {i : Nat} (hi : i < 4) : arg s₀ i = arg s₀' i := hq.2 i hi

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem SPt.agree (hp : SPre s₀) (hp' : SPre s₀') {rs : List Reg} {s₁ s₂ : State} (h₁ : SPt s₀ s₁)
    (h₂ : SPt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 4)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp]; exact hq.1) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by rw [arg_cur (h₁.esp) (h₁.args i hi), arg_cur (h₂.esp) (h₂.args i hi), spub_arg hq hi]

end

theorem SAfter.pt {s₀ : State} (hp : SPre s₀) {s : State} (h : SAfter s₀ s) : SPt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (by rw [h.mem]; exact sbig_of (sPreMem_frame s₀)) hi⟩

/-- What is known after the call. -/
structure SPost (s₀ : State) (s : State) : Prop where
  ebx : s.gpr .ebx = Kb s₀
  pt : SPt s₀ s

theorem spost_wp {s₀ : State} (hp : SPre s₀) {s : State} (h : SAfter s₀ s) : WP isa (ctrCall v.callee) s (SPost s₀) :=
  WP.mono (ctr_call v h.pre) fun s' hc => by
    have hb : below (s.gpr .esp) 28 = stkR s₀ := by rw [h.esp]; exact hp.below_eq
    have fr := hc.frame
    rw [hb, hp.cA, h.mem] at fr
    have big : Frame (SBig s₀) s₀.mem s'.mem := (sbig_of (sPreMem_frame s₀)).trans (fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨kR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
    exact ⟨by rw [hc.saved .ebx (by simp [calleeSaved]), h.pre.ebx],
      ⟨by rw [hc.saved .esp (by simp [calleeSaved]), h.esp], by rw [hc.wr, h.wr], fun _ hi => hp.arg_keep big hi⟩⟩

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysX86.pre s₀) (h0' : subkeysX86.pre s₀')
    (hq : subkeysX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  have hp := SPre.of h0
  have hp' := SPre.of h0'
  have eW : W s₀ = W s₀' := spub_arg hq (by decide)
  have eR : R s₀ = R s₀' := by rw [R, R, spub_arg hq (by decide)]
  have eK : Kb s₀ = Kb s₀' := spub_arg hq (by decide)
  have eS : Sc s₀ = Sc s₀' := spub_arg hq (by decide)
  have pt₀ : ∀ {t : State}, SPt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact SPt.agree hq hp hp' pt₀ pt₀ fun r hr => by simp at hr)
    (c := .block subkeysPre) (by taint_decide)).wp (F₁ := SAfter s₀) (F₂ := SAfter s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨spre_wp hp, spre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c := ((ctr_rel v (E := E s₀) (P := fun s₁ s₂ => SAfter s₀ s₁ ∧ SAfter s₀' s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [eW, eS, eK, eR]; exact h.2.pre, h.1.esp, h.2.esp.trans hq.1.symm⟩).wp
      (F₁ := SPost s₀) (F₂ := SPost s₀') fun _ _ h => ⟨spost_wp v hp h.1, spost_wp v hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => SPost s₀ s₁ ∧ SPost s₀' s₂) (argTaint [.ebx] (4 + 4 * 4))
    (fun _ _ h => SPt.agree hq hp hp' h.1.pt h.2.pt fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.ebx, h.2.ebx, eK])
    (c := .block subkeysPost) (by taint_decide)
  exact a.seq (c.seq b)

theorem subkeys_ct : ConstantTime isa subkeysX86.pre subkeysX86.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86
