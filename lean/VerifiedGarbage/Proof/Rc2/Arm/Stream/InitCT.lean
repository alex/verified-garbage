import VerifiedGarbage.Proof.Rc2.Arm.Stream.InitCorrect
import VerifiedGarbage.Proof.Rc2.Arm.Stream.UpdateCT

/-!
# Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` is constant time

Untrusted: everything here is checked by Lean. As for the updates
(`Stream/UpdateCT.lean`): the checks, the copy of the IV and the restore of
`lr` are checked by the taint analysis, from the public arguments; the branch
on the checks agrees in both runs, as the lengths are public; and the call of
`vg_rc2_expand_key`, in its frame, is constant time by its own proof
(`key_rel`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (eval_ne)

/-- The stack arguments after the call are those on entry. -/
theorem args_after_key (s : State) (hs : initContract.pre s) (u : State) (hu : ArgsPost s u) (v : State)
    (hk : KeyPost u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) v) :
    ∀ i < 3, stackArg v i = stackArg s i := by
  obtain ⟨_, spfit, _, _, _, _, _, _, _, ctxArgs, scrArgs, _, _, _, _, bArgs, _⟩ := hs
  have eb : below u = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, hu.sp]
  have frame₂ := hk.frame
  rw [eb] at frame₂
  intro i hi
  have hc : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s i) (32 / 8) := by
    rw [stackArgAddr_eq s hi spfit]; exact Offset.contains_base _ (by omega) (by omega)
  have ea : stackArgAddr v i = stackArgAddr s i := by unfold stackArgAddr; rw [hk.sp, hu.sp]
  rw [stackArg, ea, frame₂.readW hc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ctxArgs.symm.sub_right (Region.sub_prefix (by decide))
      · exact scrArgs.symm.sub_right (Region.sub_prefix (by decide))
      · exact bArgs.symm) (by decide)]
  refine stackArg_frame hu.frame spfit (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ctxArgs.symm.sub_right (Offset.sub_base _ (by decide))
  · exact scrArgs.symm.sub_right (Offset.sub_base _ (by decide))

theorem iwrSep {s : State} (h : initContract.pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨stackArgAddr s 0, 12⟩ r := by
  obtain ⟨_, _, _, hwr, _, _, _, _, _, ctxArgs, scrArgs, _⟩ := h
  rw [hwr]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ctxArgs.symm
  · exact scrArgs.symm

theorem checks_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) checks hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem initArgs_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) (.block initArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem tail_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [] 12) (.block (restoreLr ++ ([.mov .r0 (.imm 0)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem init_rel {s₀ s₀' : State} (h0 : initContract.pre s₀) (h0' : initContract.pre s₀')
    (hq : initContract.pub s₀ s₀') : RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have fit := h0.2.1
  have qa : ∀ i < 3, stackArg s₀ i = stackArg s₀' i := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact q₅
    · exact q₆
    · exact q₇
  have regs : ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  have hvq : IValid s₀ ↔ IValid s₀' := by simp only [IValid, q₂, q₃, q₅]
  rw [init]
  refine RelCT.seq (rel_agree (F := (· = s₀)) (F' := (· = s₀')) (G := CheckPost s₀) (G' := CheckPost s₀')
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      exact agree12 regs q₀ fit (iwrSep h0) (iwrSep h0') qa) checks_taint
    (fun s e => e ▸ checks_ok s₀ h0) (fun s e => e ▸ checks_ok s₀' h0')) ?_
  refine RelCT.ite (fun c c' ⟨hc, hc'⟩ => by
    show eval .ne c = eval .ne c'; rw [eval_ne, eval_ne, hc.z, hc'.z]; simp only [hvq]) ?_ ?_
  · exact RelCT.block_nil fun _ _ _ => trivial
  by_cases hv : IValid s₀
  swap
  · refine RelCT.of_false fun c c' ⟨⟨hc, _⟩, he⟩ => ?_
    change eval .ne c = _ at he
    rw [eval_ne, hc.z] at he; simp [hv] at he
  have hv' : IValid s₀' := hvq.mp hv
  rw [initBody]
  refine RelCT.mono (P := fun c c' => CheckPost s₀ c ∧ CheckPost s₀' c') ?_ (fun _ _ h => h.1)
    fun _ _ h => h
  refine RelCT.seq (rel_agree (G := ArgsPost s₀) (G' := ArgsPost s₀') (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun c c' hc hc' => ?_) initArgs_taint
    (fun c hc => args_ok s₀ h0 hv c hc) (fun c hc => args_ok s₀' h0' hv' c hc)) ?_
  · have g : ∀ {s c}, IValid s → CheckPost s c → ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), c.gpr r = s.gpr r :=
      fun hv hc r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hc.ok hv
        all_goals exact hc.keep _ (by decide) (by decide)
    have st : ∀ {s c}, CheckPost s c → ∀ i, stackArg c i = stackArg s i := fun hc i => by
      unfold stackArg stackArgAddr; rw [hc.mem, hc.sp]
    exact agree12 (fun r hr => by rw [g hv hc r hr, g hv' hc' r hr]; exact regs r hr)
      (by rw [hc.sp, hc'.sp, q₀]) (by rw [hc.sp]; exact fit)
      (by rw [hc.wr, show stackArgAddr c 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [hc.sp]]
          exact iwrSep h0)
      (by rw [hc'.wr, show stackArgAddr c' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [hc'.sp]]
          exact iwrSep h0')
      (fun i hi => by rw [st hc, st hc']; exact qa i hi)
  have hct : RelCT isa (fun u u' => ArgsPost s₀ u ∧ ArgsPost s₀' u') keyCall fun _ _ => True :=
    key_rel (sp₀ := s₀.sp) fun u u' ⟨a, a'⟩ => ⟨key_pre s₀ h0 hv u a, by
      have := key_pre s₀' h0' hv' u' a'; rwa [← q₁, ← q₂, ← q₃, ← q₆, ← q₇] at this, a.sp, a'.sp.trans q₀.symm⟩
  refine RelCT.seq (rel_wp (G := fun v => ∃ u, ArgsPost s₀ u ∧
      KeyPost u (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r2) (stackArg s₀ 1) (stackArg s₀ 2) v)
    (G' := fun v => ∃ u, ArgsPost s₀' u ∧
      KeyPost u (s₀'.gpr .r0) (s₀'.gpr .r1) (s₀'.gpr .r2) (stackArg s₀' 1) (stackArg s₀' 2) v) hct
    (fun u a => WP.mono (key_call (key_pre s₀ h0 hv u a)) fun v hk => ⟨u, a, hk⟩)
    (fun u a => WP.mono (key_call (key_pre s₀' h0' hv' u a)) fun v hk => ⟨u, a, hk⟩)) ?_
  refine (rel_agree (argTaint [] 12) (fun v v' ⟨u, a, k⟩ ⟨u', a', k'⟩ => ?_) tail_taint
    (fun v ⟨u, a, k⟩ => WP.mono (tail_ok s₀ h0 hv u a v k) fun _ _ => trivial)
    (fun v ⟨u, a, k⟩ => WP.mono (tail_ok s₀' h0' hv' u a v k) fun _ _ => trivial)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  exact agree12 (fun r hr => (List.not_mem_nil hr).elim) (by rw [k.sp, a.sp, k'.sp, a'.sp, q₀])
    (by rw [k.sp, a.sp]; exact fit)
    (by rw [k.wr, a.wr, show stackArgAddr v 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [k.sp, a.sp]]
        exact iwrSep h0)
    (by rw [k'.wr, a'.wr, show stackArgAddr v' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [k'.sp, a'.sp]]
        exact iwrSep h0')
    (fun i hi => by
      rw [args_after_key s₀ h0 u a v k i hi, args_after_key s₀' h0' u' a' v' k' i hi]; exact qa i hi)

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Rc2.Arm.Stream
