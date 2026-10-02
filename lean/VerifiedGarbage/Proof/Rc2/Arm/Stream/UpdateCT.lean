import VerifiedGarbage.Proof.Rc2.Arm.Stream.Update
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Streaming RC2-CBC on ARMv7: the update functions are constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the test of
`out_len`, the copies before the call and the restore of `lr` after it are
checked by the taint analysis, from the public arguments (in registers and on
the stack), whose values in each run the correctness proofs pin; the branch on
`out_len` agrees in both runs; and the call of the CBC function, in its frame,
is constant time by its own proof (`cbc_rel`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (eval_eq)

theorem wp_nil_inv {s : State} {Q : State → Prop} (h : WP isa (.block []) s Q) : Q s := by
  obtain ⟨_, _, he, hq⟩ := h
  cases he with
  | block h => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]; exact hq

theorem sa0' (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  unfold stackArgAddr; rw [show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp from BitVec.add_zero _]

/-- Two states agree on the registers `rs` and the 12 bytes of stack arguments. -/
theorem agree12 {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (hsp : s₁.sp = s₂.sp)
    (fit : s₁.sp.toNat + 12 ≤ 2 ^ 32)
    (hw₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨stackArgAddr s₁ 0, 12⟩ r)
    (hw₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨stackArgAddr s₂ 0, 12⟩ r)
    (ha : ∀ i < 3, stackArg s₁ i = stackArg s₂ i) : VG.Arm.Taint.Agree (argTaint rs 12) s₁ s₂ :=
  agree_argTaint h hsp ⟨fit, by rw [← sa0']; exact hw₁⟩ ⟨hsp ▸ fit, by rw [← sa0']; exact hw₂⟩
    (argMem_of (j := 3) hsp fit ha)

/-- The code before the call, its pieces associated to the left. -/
def prefixL : Prog isa :=
  .seq (.seq (.seq (.seq (.seq (.seq (.block toOut) (copy .r0 136 .lr 0 .r1)) (.block middle))
    (copy .r2 0 .lr 0 .r1)) (.block toPending)) (copy .r2 0 .lr 136 .r3)) (.block cbcArgs)

theorem prefix_wp (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Keep s t) : WP isa prefixL t (Mid s) := by
  have h := long_ok' d s hs hnz t ht (tail := .block []) (Q := Mid s) fun t' h => WP.block_nil h
  rw [longWith] at h
  have h := WP.assoc' (WP.assoc' (WP.assoc' (WP.assoc' (WP.assoc' (WP.assoc' h)))))
  exact WP.mono (WP.seq_iff.mp h) fun _ h => wp_nil_inv h

theorem b0_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12)
    (.block [.ldrSp .r12 4, .cmp .r12 (.imm 0)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem short_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) short hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem prefix_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) prefixL hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem restore_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 12) (.block restoreLr) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem stackArg_keep {s t : State} (ht : Keep s t) (i : Nat) : stackArg t i = stackArg s i := by
  unfold stackArg stackArgAddr; rw [ht.mem, ht.sp]

theorem wrSep (d : Spec.Rc2.Direction) {s : State} (h : (updateContract d).pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨stackArgAddr s 0, 12⟩ r := by
  obtain ⟨_, _, _, hwr, _, _, _, ctxArgs, _, _, _, outArgs, scrArgs, _⟩ := h
  rw [hwr]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ctxArgs.symm
  · exact outArgs.symm
  · exact scrArgs.symm

theorem update_rel (d : Spec.Rc2.Direction) {s₀ s₀' : State} (h0 : (updateContract d).pre s₀)
    (h0' : (updateContract d).pre s₀') (hq : (updateContract d).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update d) fun _ _ => True := by
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
  have keepAgree : ∀ t t', Keep s₀ t → Keep s₀' t' →
      VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] 12) t t' := fun t t' k k' =>
    agree12 (fun r hr => by
        have hr12 : r ≠ .r12 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> decide
        rw [k.reg r hr12, k'.reg r hr12]; exact regs r hr)
      (by rw [k.sp, k'.sp, q₀]) (by rw [k.sp]; exact fit)
      (by rw [k.wr, show stackArgAddr t 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [k.sp]]; exact wrSep d h0)
      (by rw [k'.wr, show stackArgAddr t' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [k'.sp]]
          exact wrSep d h0')
      (fun i hi => by rw [stackArg_keep k, stackArg_keep k']; exact qa i hi)
  rw [update]
  refine RelCT.seq (rel_agree (F := (· = s₀)) (F' := (· = s₀'))
    (G := fun t => Keep s₀ t ∧ t.z = decide ((stackArg s₀ 1).toNat = 0))
    (G' := fun t => Keep s₀' t ∧ t.z = decide ((stackArg s₀' 1).toNat = 0))
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      exact agree12 regs q₀ fit (wrSep d h0) (wrSep d h0') qa) b0_taint
    (fun s e => e ▸ b0_wp d s₀ h0) (fun s e => e ▸ b0_wp d s₀' h0')) ?_
  refine RelCT.ite (fun t t' ⟨⟨_, z⟩, ⟨_, z'⟩⟩ => by
    show eval .eq t = eval .eq t'; rw [eval_eq, eval_eq, z, z', q₆]) ?_ ?_
  · refine (rel_agree (F := fun t => Keep s₀ t ∧ (stackArg s₀ 1).toNat = 0)
      (F' := fun t => Keep s₀' t ∧ (stackArg s₀' 1).toNat = 0) (G := fun _ => True) (G' := fun _ => True)
      (argTaint [.r0, .r1, .r2, .r3] 12) (fun t t' k k' => keepAgree t t' k.1 k'.1) short_taint
      (fun t k => WP.mono (short_ok d s₀ h0 k.2 t k.1) fun _ _ => trivial)
      (fun t k => WP.mono (short_ok d s₀' h0' k.2 t k.1) fun _ _ => trivial)).mono ?_ fun _ _ _ => trivial
    rintro t t' ⟨⟨⟨k, z⟩, ⟨k', z'⟩⟩, he⟩
    have h1 : (stackArg s₀ 1).toNat = 0 := by
      change eval .eq t = _ at he
      rw [eval_eq, z] at he; exact of_decide_eq_true (Option.some.inj he)
    exact ⟨⟨k, h1⟩, ⟨k', by rw [← q₆]; exact h1⟩⟩
  by_cases hz0 : (stackArg s₀ 1).toNat = 0
  · refine RelCT.of_false fun t t' ⟨⟨⟨_, z⟩, _⟩, he⟩ => ?_
    change eval .eq t = _ at he
    rw [eval_eq, z, hz0] at he; simp at he
  have hz0' : (stackArg s₀' 1).toNat ≠ 0 := by rw [← q₆]; exact hz0
  rw [long_eq, longWith]
  apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc
  apply RelCT.assoc
  refine RelCT.mono (P := fun t t' => (Keep s₀ t ∧ (stackArg s₀ 1).toNat ≠ 0) ∧
    (Keep s₀' t' ∧ (stackArg s₀' 1).toNat ≠ 0)) ?_ ?_ fun _ _ h => h
  · refine RelCT.seq (rel_agree (F := fun t => Keep s₀ t ∧ (stackArg s₀ 1).toNat ≠ 0)
      (F' := fun t => Keep s₀' t ∧ (stackArg s₀' 1).toNat ≠ 0) (G := Mid s₀) (G' := Mid s₀')
      (argTaint [.r0, .r1, .r2, .r3] 12) (fun t t' k k' => keepAgree t t' k.1 k'.1) prefix_taint
      (fun t k => prefix_wp d s₀ h0 k.2 t k.1) (fun t k => prefix_wp d s₀' h0' k.2 t k.1)) ?_
    have hct : RelCT isa (fun t t' => Mid s₀ t ∧ Mid s₀' t') (cbcCall d) fun _ _ => True :=
      cbc_rel (sp₀ := s₀.sp) fun t t' ⟨m, m'⟩ => ⟨mid_pre d s₀ h0 t m, by
        have := mid_pre d s₀' h0' t' m'; rwa [← q₁, ← q₅, ← q₆, ← q₇] at this, m.sp, m'.sp.trans q₀.symm⟩
    refine RelCT.seq (rel_wp (G := fun u => ∃ t, Mid s₀ t ∧ CbcPost d t (s₀.gpr .r0) (s₀.gpr .r0 + 128)
        (stackArg s₀ 0) (BitVec.ofNat 32 ((stackArg s₀ 1).toNat / 8)) (stackArg s₀ 2) u)
      (G' := fun u => ∃ t, Mid s₀' t ∧ CbcPost d t (s₀'.gpr .r0) (s₀'.gpr .r0 + 128)
        (stackArg s₀' 0) (BitVec.ofNat 32 ((stackArg s₀' 1).toNat / 8)) (stackArg s₀' 2) u) hct
      (fun t m => WP.mono (cbc_call (mid_pre d s₀ h0 t m)) fun u hu => ⟨t, m, hu⟩)
      (fun t m => WP.mono (cbc_call (mid_pre d s₀' h0' t m)) fun u hu => ⟨t, m, hu⟩)) ?_
    refine rel_agree (argTaint [] 12) (fun u u' ⟨t, m, c⟩ ⟨t', m', c'⟩ => ?_) restore_taint
      (fun u ⟨t, m, c⟩ => WP.mono (restore_ok d s₀ h0 hz0 t m u c) fun _ _ => trivial)
      (fun u ⟨t, m, c⟩ => WP.mono (restore_ok d s₀' h0' hz0' t m u c) fun _ _ => trivial) |>.mono
      (fun _ _ h => h) fun _ _ _ => trivial
    exact agree12 (fun r hr => (List.not_mem_nil hr).elim) (by rw [c.sp, m.sp, c'.sp, m'.sp, q₀])
      (by rw [c.sp, m.sp]; exact fit)
      (by rw [c.wr, m.wr, show stackArgAddr u 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [c.sp, m.sp]]
          exact wrSep d h0)
      (by rw [c'.wr, m'.wr, show stackArgAddr u' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [c'.sp, m'.sp]]
          exact wrSep d h0')
      (fun i hi => by rw [args_after d s₀ h0 t m u c i hi, args_after d s₀' h0' t' m' u' c' i hi]; exact qa i hi)
  · intro t t' ⟨⟨⟨k, _⟩, ⟨k', _⟩⟩, _⟩
    exact ⟨⟨k, hz0⟩, ⟨k', hz0'⟩⟩

theorem update_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (updateContract d).pre (updateContract d).pub (update d) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel d h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Rc2.Arm.Stream
