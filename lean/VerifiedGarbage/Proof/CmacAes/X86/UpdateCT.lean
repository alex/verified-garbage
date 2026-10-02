import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
import VerifiedGarbage.Proof.Framework.X86.ArgTaint

/-!
# AES-CMAC on x86: `vg_cmac_aes_update` is constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the taint
analysis covers the code between the calls, from `esp`, the stack arguments
(which nothing writes, `argTaint`) and `esi` (the next block, which the
correctness proof pins to the public arguments), and each call of
`vg_aes_ctr32`, in its frame, is constant time by its own proof (`ctr_rel`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (eval_e eval_ne)

/-- The stack arguments of a state with the entry stack pointer, from
those of the entry state. -/
theorem arg_cur {s₀ s : State} (hesp : s.gpr .esp = s₀.gpr .esp) {i : Nat}
    (hm : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) : arg s i = arg s₀ i := by
  show s.mem.readW (argAddr s i) 32 = _
  rw [show argAddr s i = argAddr s₀ i by simp only [argAddr, hesp]]; exact hm

theorem UPre.argsOut {s₀ : State} (hp : UPre s₀) {s : State} (hesp : s.gpr .esp = E s₀) (hwr : s.wr = s₀.wr) :
    ArgsOut 6 s := by
  have hs : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.args_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.args_scr

/-- What two runs agree on at a point between the calls. -/
structure Pt (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = E s₀
  wr : s.wr = s₀.wr
  args : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

section
variable {s₀ s₀' : State} (hq : updateX86.pub s₀ s₀')
include hq

theorem pub_E : E s₀ = E s₀' := hq.1
theorem pub_arg {i : Nat} (hi : i < 6) : arg s₀ i = arg s₀' i := hq.2 i hi
theorem pub_N : N s₀ = N s₀' := by rw [N, N, pub_arg hq (by decide)]
theorem pub_W : W s₀ = W s₀' := pub_arg hq (by decide)
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_arg hq (by decide)]
theorem pub_St : St s₀ = St s₀' := pub_arg hq (by decide)
theorem pub_Dp : Dp s₀ = Dp s₀' := pub_arg hq (by decide)
theorem pub_S : S s₀ = S s₀' := pub_arg hq (by decide)
theorem pub_Cb : Cb s₀ = Cb s₀' := by rw [Cb, Cb, pub_S hq]

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem Pt.agree (hp : UPre s₀) (hp' : UPre s₀') {rs : List Reg} {s₁ s₂ : State} (h₁ : Pt s₀ s₁)
    (h₂ : Pt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp, pub_E hq]) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by rw [arg_cur (h₁.esp) (h₁.args i hi), arg_cur (h₂.esp) (h₂.args i hi), pub_arg hq hi]

end

theorem LInv.pt {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv s₀ k s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (UPre.big_of h.frame) hi⟩

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CtrPre s (W s₀) (Cb s₀) (St s₀) (S s₀) (R s₀)
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k)
  pt : Pt s₀ s
  big : Frame (Big s₀) s₀.mem s.mem

theorem bodyMid_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block chainIn) s (Mid s₀ k) :=
  WP.mono (bodyA_wp hp hk h) fun s₁ a => by
    have big : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (by
      rw [a.mem]
      exact (Proof.Cmac.chainMem4_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
        · exact ⟨stR s₀, by simp, fun _ h => h⟩)
    exact ⟨a.pre, by rw [a.esi, h.esi], ⟨by rw [a.esp, h.esp], by rw [a.wr, h.wr],
      fun _ hi => hp.arg_keep big hi⟩, big⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k)
  pt : Pt s₀ s

theorem call_after {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : Mid s₀ k s) :
    WP isa ctrCall s (After s₀ k) :=
  WP.mono (ctr_call h.pre) fun s' hc => by
    have hb : below (s.gpr .esp) 28 = stkR s₀ := by rw [h.pt.esp]; exact hp.below_eq
    have cA : (Cb s₀).setWidth 64 = (S s₀).setWidth 64 + BitVec.ofNat 64 2048 := hp.scrA (by decide)
    have fr := hc.frame
    rw [hb, cA] at fr
    have big : Frame (Big s₀) s₀.mem s'.mem := h.big.trans (fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
    exact ⟨by rw [hc.saved .esi (by simp [calleeSaved]), h.esi],
      ⟨by rw [hc.saved .esp (by simp [calleeSaved]), h.pt.esp], by rw [hc.wr, h.pt.wr],
        fun _ hi => hp.arg_keep big hi⟩⟩

/-- The relation before a block, in two runs. -/
def BRel (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (k < N s₀ ∧ LInv s₀ k s₁) ∧ (k < N s₀' ∧ LInv s₀' k s₂)

theorem body_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updateX86.pub s₀ s₀') (k : Nat) :
    RelCT isa (BRel s₀ s₀' k) body fun _ _ => True := by
  have a := ((RelCT.taint (A := taint) (P := BRel s₀ s₀' k) (argTaint [.esi] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp hp' (h.1.2.pt hp) (h.2.2.pt hp') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.esi, h.2.2.esi, pub_Dp hq])
    (c := .block chainIn) (by taint_decide)).wp (F₁ := Mid s₀ k) (F₂ := Mid s₀' k)
      fun _ _ h => ⟨bodyMid_wp hp h.1.1 h.1.2, bodyMid_wp hp' h.2.1 h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have c := ((ctr_rel (E := E s₀) (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_Cb hq, pub_St hq, pub_S hq, pub_R hq]; exact h.2.pre, h.1.pt.esp,
        h.2.pt.esp.trans (pub_E hq).symm⟩).wp (F₁ := After s₀ k) (F₂ := After s₀' k)
      fun _ _ h => ⟨call_after hp h.1, call_after hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂)
    (argTaint [.esi] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp hp' h.1.pt h.2.pt fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.esi, h.2.esi, pub_Dp hq])
    (c := .block advance) (by taint_decide)
  exact a.seq (c.seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ BRel s₀ s₀' k s₁ s₂

theorem loop_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updateX86.pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop body .ne) fun s₁ s₂ => LInv s₀ (N s₀) s₁ ∧ LInv s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (body_ct hp hp' hq k).wp
    (F₁ := fun (s : State) => (LInv s₀ (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀))) ∧ k < N s₀)
    (F₂ := fun (s : State) => LInv s₀' (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀')))
    fun _ _ h => ⟨WP.mono (body_ok hp h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩, body_ok hp' h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hk⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₁ = _; rw [eval_ne, z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + 1 = N s₀ := by simpa using hf
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : k + 1 ≠ N s₀ := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, ⟨by omega, l₁⟩, ⟨by omega, l₂⟩⟩

/-! ## The whole function -/

theorem update_rel {s₀ s₀' : State} (h0 : updateX86.pre s₀) (h0' : updateX86.pre s₀')
    (hq : updateX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') update fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  have pt₀ : ∀ {t : State}, UPre t → Pt t t := fun h => ⟨rfl, rfl, fun _ _ => rfl⟩
  have pro := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact Pt.agree hq hp hp' (pt₀ hp) (pt₀ hp') fun r hr => by simp at hr)
    (c := .block setup) (by taint_decide)).wp
    (F₁ := fun (s : State) => LInv s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)))
    (F₂ := fun (s : State) => LInv s₀' 0 s ∧ s.zf = some (decide (N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have ev {s : State} (h : s.zf = some (decide (N s₀ = 0))) : isa.eval .e s = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, h]
  have ev' {s : State} (h : s.zf = some (decide (N s₀' = 0))) : isa.eval .e s = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0)))) ∧ isa.eval .e a = some true) (argTaint [] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp hp' (h.1.1.1.pt hp) (h.1.2.1.pt hp') fun r hr => by simp at hr)
    (c := .block []) (by taint_decide)
  have mid : RelCT isa (fun a b => (LInv s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0))))
      (.ite .e (.block []) (.loop body .ne)) (fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv s₀ (N s₀)) (F₂ := LInv s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ⟨?_, h.1.1.1⟩, ⟨?_, h.1.2.1⟩⟩)
        fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.2] at this
        have : N s₀ ≠ 0 := by simpa using this
        omega
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b)
    (argTaint [] (4 + 4 * 6)) (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (c := .block (restore 5)) (by taint_decide)
  exact pro.seq (mid.seq epi)

theorem update_ct : ConstantTime isa updateX86.pre updateX86.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86
