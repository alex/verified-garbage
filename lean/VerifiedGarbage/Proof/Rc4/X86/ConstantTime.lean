import VerifiedGarbage.Proof.Rc4.X86.Contract
import VerifiedGarbage.Proof.Rc4.X86.Lit
import VerifiedGarbage.Proof.Rc4.X86.Apply
import VerifiedGarbage.Proof.Framework.RelCT

/-! # RC4 on x86 (32-bit): constant time

Initialization is checked by the taint analysis alone. The stream function
first loads the PRGA index `i` from the context, which the analysis takes
for secret: the contract lets it leak, so the proof makes it public by hand
(`entry_ct`) and the analysis checks the rest.
-/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-! ## Initialization -/

def initTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [258, 64],
    argLen := 20, argBases := [(12, 0), (16, 1)] }

theorem initTaint_wf {s : State} (hs : initC.pre s) : VG.X86.Taint.Wf initTaint s := by
  obtain ⟨_, hwr, _, _, cs, ac, as, rc, rs, _, cfit, sfit, spfit⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spfit, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨cs, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rc ac
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rs as
  · intro p hp
    simp only [initTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem initTaint_agree {s t : State} (hs : initC.pre s) (ht : initC.pre t) (hp : initC.pub s t) :
    VG.X86.Taint.Agree initTaint s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, initC.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, initTaint_wf hs,
    initTaint_wf ht, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [initTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 2 (by decide), args 3 (by decide)]
  · simp only [initTaint] at hk
    rw [show VG.X86.Taint.depth initTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem init_ct : ConstantTime isa initC.pre initC.pub init :=
  VG.Taint.constantTime (A := taint) initTaint (fun _ _ h₁ h₂ hp => initTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The stream function -/

def applyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [258, 0, 64],
    argLen := 20, argBases := [(4, 0), (8, 1), (16, 2)] }

/-- After `entry`, with `i` in `eax`. -/
def loopTaint : VG.X86.Taint.T := { applyTaint with regs := .ofList [.esp, .eax] }

theorem applyTaint_wf {s : State} (hs : applyC.pre s) : VG.X86.Taint.Wf applyTaint s := by
  obtain ⟨_, hwr, cd, cs, ds, ac, ad, as, rc, rd, rs, cfit, dfit, sfit, spfit⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spfit, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨cd, cs⟩, ds, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rc ac
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rd ad
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rs as
  · intro p hp
    simp only [applyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem applyTaint_agree {s t : State} (hs : applyC.pre s) (ht : applyC.pre t)
    (sp : s.gpr .esp = t.gpr .esp) (args : ∀ i < 4, arg s i = arg t i) :
    VG.X86.Taint.Agree applyTaint s t := by
  have fit : ∀ s, applyC.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, applyTaint_wf hs,
    applyTaint_wf ht, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [applyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 0 (by decide), args 1 (by decide), args 2 (by decide),
      args 3 (by decide)]
  · simp only [applyTaint] at hk
    rw [show VG.X86.Taint.depth applyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem applyPre_of {s : State} (hs : applyC.pre s) :
    ApplyPre s (arg s 0) (arg s 1) (arg s 2) (arg s 3) := by
  obtain ⟨hrd, hwr, cd, cs, ds, ac, ad, as, _, _, _, cfit, dfit, sfit, spfit⟩ := hs
  exact
    { aP := rfl, aD := rfl, aL := rfl, aS := rfl
      args := ⟨_, by rw [hrd]; exact List.mem_singleton_self _, Region.contains_self _ _⟩
      ctx := ⟨_, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
      data := ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        Region.contains_self _ _⟩
      scratch := ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), Region.contains_self _ _⟩
      ctxFit := cfit, dataFit := dfit, scratchFit := sfit, spFit := spfit
      ctxData := cd, ctxScratch := cs, dataScratch := ds
      argsCtx := ac, argsData := ad, argsScratch := as }

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem entry_ct : RelCT isa (fun a b => applyC.pre a ∧ applyC.pre b ∧ applyC.pub a b)
    (.block entry) fun a b => VG.X86.Taint.Agree loopTaint a b ∧ a.zf = b.zf := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hsp, hargs, hi⟩ ea eb
  have hag := applyTaint_agree hpa hpb hsp hargs
  obtain ⟨htrace, -⟩ := RelCT.taint (A := taint) (P := fun a b => VG.X86.Taint.Agree applyTaint a b)
    applyTaint (fun _ _ h => h) (by taint_decide) a b tr tr' a' b' hag ea eb
  obtain ⟨_, u, eu, ham, hak, hax, haz⟩ := apply_entry a (applyPre_of hpa)
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbm, hbk, hbx, hbz⟩ := apply_entry b (applyPre_of hpb)
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  have hi' : (contextAt a.mem ((arg a 0).setWidth 64)).i =
      (contextAt b.mem ((arg b 0).setWidth 64)).i :=
    BitVec.eq_of_toNat_eq (List.cons.inj hi).1
  have hsp₁ : u.gpr .esp = a.gpr .esp := hak.gpr (by decide)
  have hsp₂ : v.gpr .esp = b.gpr .esp := hbk.gpr (by decide)
  refine ⟨htrace, VG.X86.Taint.Agree.keep hag ⟨fun r hr => ?_, fun h => nomatch h⟩ rfl rfl rfl rfl
    rfl hak.2.2 hbk.2.2 ham hbm hsp₁ hsp₂ (fun _ h => (List.not_mem_nil h).elim)
    (fun _ h => (List.not_mem_nil h).elim), ?_⟩
  · simp only [loopTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hsp₁, hsp₂, hsp]
    · rw [hax, hbx, hi']
  · rw [haz, hbz, hargs 2 (by decide)]

theorem nil_ct {P : State → State → Prop} : RelCT isa P (.block []) fun _ _ => True := by
  intro _ _ _ _ _ _ _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  exact ⟨e₁.2.symm.trans e₂.2, trivial⟩

theorem apply_ct : ConstantTime isa applyC.pre applyC.pub apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold apply
  refine RelCT.seq entry_ct (RelCT.ite ?_ nil_ct ?_)
  · intro a b ⟨_, hz⟩
    simp only [eval, hz]
  · exact RelCT.taint (A := taint) loopTaint (fun _ _ h => h.1.1) (by taint_decide)

end VG.Proof.Rc4.X86
