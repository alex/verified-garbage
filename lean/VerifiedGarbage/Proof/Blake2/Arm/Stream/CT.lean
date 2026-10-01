import VerifiedGarbage.Proof.Blake2.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Sig

/-!
# Streaming BLAKE2 on ARMv7: constant time

Untrusted: everything here is checked by Lean. The taint analysis does not
analyse frames, so `update` and `finalize`, whose calls are in frames, are
proven constant time by relating two runs (`RelCT`), piece by piece: the code
between the calls by the taint analysis, from the public arguments for the
prologue and from the registers holding our variables afterwards (which the
correctness proofs determine from the public arguments), and each call by the
compression function's contract (`call_rel`: `RelCT.frame`, `RelCT.call`).
The pieces do not depend on the compression function, so the taint analysis
checks them here, for both word sizes.
-/

namespace VG.Proof.Blake2.Arm.Stream

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (call updatePro updateMid updateEnd update finalizePro finalizeEnd finalize)

/-! ## The taint on entry -/

/-- The taint in which the registers `rs` and the first `n` bytes of stack
arguments are public. -/
def argTaint (rs : List Reg) (n : Nat) : VG.Arm.Taint.T :=
  { regs := RegSet.ofList rs, flags := false, argLen := n }

/-- The first `4 j` bytes of stack arguments agree when their first `j` words do. -/
theorem argMem_of {s₁ s₂ : State} {j : Nat} (hsp : s₁.sp = s₂.sp) (hf : s₁.sp.toNat + 4 * j ≤ 2 ^ 32)
    (h : ∀ i < j, stackArg s₁ i = stackArg s₂ i) :
    ∀ k < 4 * j, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  intro k hk
  have e : ∀ s : State, s.sp.toNat + 4 * j ≤ 2 ^ 32 →
      VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := fun s hs => by
    simp only [VG.Arm.Taint.argByte, stackArgAddr]
    rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [e s₁ hf, e s₂ (hsp ▸ hf), Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
    Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (h _ (by omega))

theorem agree_argTaint {rs : List Reg} {n : Nat} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : s₁.sp = s₂.sp)
    (hw₁ : s₁.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s₁.wr, Region.Disjoint ⟨State.addr s₁.sp, n⟩ r)
    (hw₂ : s₂.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s₂.wr, Region.Disjoint ⟨State.addr s₂.sp, n⟩ r)
    (hm : ∀ k < n, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k)) :
    VG.Arm.Taint.Agree (argTaint rs n) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ => hw₁,
    fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ => hw₂,
    fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp _ := hsp
  argMem := hm

/-- Code the taint analysis checks from `τ`, in two runs whose single-run
facts `F` and `F'` make them agree on it. -/
theorem rel_agree {F F' G G' : State → Prop} {c : Prog isa} (τ : VG.Arm.Taint.T)
    (hag : ∀ s s', F s → F' s' → VG.Arm.Taint.Agree τ s s')
    (hc : ∃ hc, (VG.Taint.check taint τ c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) τ (fun s s' h => hag s s' h.1 h.2) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-! ## The calls in two runs -/

theorem push_eq {rs : List Reg} {s a : State} (hrs : regList rs = true) (h : isa.push (.push rs) s = some a) :
    a = pushed rs s := by
  rw [push_pushed hrs (by
    simp only [isa, push] at h; split at h <;> [skip; cases h]
    rename_i hc; exact hc.2)] at h
  exact (Option.some.inj h).symm

/-- A call of the compression function, in its frame, leaks the same in two
runs whose arguments are the same, and whose stack pointers are. -/
theorem call_rel {w : Nat} {P : Params w} {name : String} {code : Prog isa} (hf : CalleeOk P code)
    {Rel : State → State → Prop} {sp st scr blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
    (h : ∀ s s', Rel s s' → CallArgs (w := w) s st scr blk n t last ∧ CallArgs (w := w) s' st scr blk n t last ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa Rel (call name code) fun _ _ => True := by
  refine RelCT.frame (fun s s' hp => by obtain ⟨-, -, e, e'⟩ := h s s' hp; rw [e, e']) ?_
  refine RelCT.call hf.verified.1 hf.verified.2.1 (CallArgs.rd w sp blk n) (CallArgs.wr w st scr)
    fun a b ⟨s, s', hp, pa, pb⟩ => ?_
  obtain ⟨u, u', e, e'⟩ := h s s' hp
  rw [push_eq rfl pa, push_eq rfl pb]
  subst e
  have v : s'.sp = s.sp := e'
  have hv' : CallArgs.rd w s.sp blk n = CallArgs.rd w s'.sp blk n := by rw [v]
  have t1 : ((pushed args4 s).callEntry.withRegions (CallArgs.rd w s.sp blk n) (CallArgs.wr w st scr)).sp =
    s.sp - 16 := CallArgs.psp
  have t2 : ((pushed args4 s').callEntry.withRegions (CallArgs.rd w s.sp blk n) (CallArgs.wr w st scr)).sp =
    s'.sp - 16 := CallArgs.psp
  refine ⟨u.pre, hv' ▸ u'.pre, ?_, u.cov, u.covW, hv' ▸ u'.cov, u'.covW⟩
  obtain ⟨c11, c3⟩ := BitVec.append_32_inj (u.t.trans u'.t.symm)
  simp only [compressArm]
  refine ⟨by rw [t1, t2, v], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, ce0, pushed_gpr, u.r0, u'.r0]
  · simp only [State.withRegions_gpr, ce1, pushed_gpr, u.r1, u'.r1]
  · simp only [State.withRegions_gpr, ce2, pushed_gpr, u.r2, u'.r2]
  · rw [u.arg0 _ t1 rfl, u'.arg0 _ t2 rfl, c3]
  · rw [u.arg1 _ t1 rfl, u'.arg1 _ t2 rfl, c11]
  · rw [u.arg2 _ t1 rfl, u'.arg2 _ t2 rfl]
  · rw [u.arg3 _ t1 rfl, u'.arg3 _ t2 rfl]

end VG.Proof.Blake2.Arm.Stream

/-! ## `update` -/

namespace VG.Proof.Blake2.Arm.Stream.Update

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (call updatePro updateMid updateEnd update)
open VG.Proof.Blake2 (updateArm countArm)

/-- The registers holding our variables. -/
abbrev vars : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The pieces of `update` between its calls pass the taint analysis. -/
theorem checks {w : Nat} {P : Params w} (hP : Ok P) :
    (∃ hc, (VG.Taint.check taint (argTaint [.r0, .r2, .r3] 12) (updatePro (w := w)) hc).isSome = true) ∧
    (∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs vars) (updateMid (w := w)) hc).isSome = true) ∧
    (∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs vars) (updateEnd (w := w)) hc).isSome = true) := by
  rcases hP.w with rfl | rfl <;> exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

section CT
variable {w : Nat} {P : Params w} {s₀ s₀' : State} (hpub : (updateArm P).pub s₀ s₀')
include hpub

theorem st_eq : st s₀' = st s₀ := hpub.2.1.symm
theorem dp_eq : dp s₀' = dp s₀ := hpub.2.2.2.2.1.symm
theorem len_eq : len s₀' = len s₀ := by simp only [len, hpub.2.2.2.2.2.1]
theorem scr_eq : scr s₀' = scr s₀ := hpub.2.2.2.2.2.2.symm
theorem cnt_eq : cnt s₀' = cnt s₀ := by simp only [cnt, countArm, hpub.2.2.1, hpub.2.2.2.1]
theorem a₁_eq' : a₁ w s₀' = a₁ w s₀ := by simp only [a₁, r₀, len_eq hpub, cnt_eq hpub]
theorem n₁_eq : n₁ w s₀' = n₁ w s₀ := by simp only [n₁, r₀, a₁_eq' hpub, len_eq hpub, cnt_eq hpub]
theorem r₂_eq : r₂ w s₀' = r₂ w s₀ := by simp only [r₂, r₀, a₁_eq' hpub, len_eq hpub, cnt_eq hpub]
theorem k₂_eq : k₂ w s₀' = k₂ w s₀ := by simp only [k₂, a₁_eq' hpub, len_eq hpub]
theorem blk₂_eq : blk₂ w s₀' = blk₂ w s₀ := by
  simp only [blk₂, a₁_eq' hpub, len_eq hpub, st_eq hpub, dp_eq hpub]

/-- The variables agree in two runs whose states are `Common` at the same
point, with the same number of buffered bytes. -/
theorem vars_agree {c r : Nat} {s s' : State} (h : Common w s₀ c s) (h' : Common w s₀' c s')
    (h8 : s.gpr .r8 = BitVec.ofNat 32 r) (h8' : s'.gpr .r8 = BitVec.ofNat 32 r) :
    ∀ x ∈ vars, s.gpr x = s'.gpr x := by
  have hc := (h.cn.trans (by rw [cnt_eq hpub])).trans h'.cn.symm
  obtain ⟨c10, c9⟩ := BitVec.append_32_inj hc
  intro x hx
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r4, h'.r4, st_eq hpub]
  · rw [h.r5, h'.r5, scr_eq hpub]
  · rw [h.r6, h'.r6, dp_eq hpub]
  · rw [h.r7, h'.r7, len_eq hpub]
  · rw [h8, h8']
  · exact c9
  · exact c10

theorem update_rel (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code)
    (hp : Pre w s₀) (hp' : Pre w s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (update (w := w) name code) fun _ _ => True := by
  obtain ⟨c₁, c₂, c₃⟩ := checks hP
  have hsp : s₀.sp = s₀'.sp := hpub.1
  have wfA : ∀ {s : State}, Pre w s →
      s.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 12⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 12⟩ : Region) = argR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.a_st
    · exact h.a_scr
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := PostPro P s₀)
    (G' := PostPro P s₀') (argTaint [.r0, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (argMem_of (j := 3) hsp hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hpub.2.1
        · exact hpub.2.2.1
        · exact hpub.2.2.2.1
      · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact hpub.2.2.2.2.1
        · exact hpub.2.2.2.2.2.1
        · exact hpub.2.2.2.2.2.2) c₁
    (fun s e => by rw [e]; exact pro_ok hP hp) (fun s e => by rw [e]; exact pro_ok hP hp')
  have call₁ : RelCT isa (fun s₁ s₂ => PostPro P s₀ s₁ ∧ PostPro P s₀' s₂) (call name code)
      fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂ :=
    ((call_rel hf (sp := s₀.sp) fun s s' ⟨h, h'⟩ => by
      have a := h'.2
      rw [st_eq hpub, scr_eq hpub, n₁_eq hpub, cnt_eq hpub, a₁_eq' hpub] at a
      exact ⟨h.2, a, h.1.sp, h'.1.sp.trans hsp.symm⟩).wp
      fun s s' h => ⟨call₁_ok hP hf hp h.1, call₁_ok hP hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have mid := rel_agree (F := Mid P s₀) (F' := Mid P s₀') (VG.Arm.Taint.ofRegs vars)
    (fun s s' h h' => VG.Arm.Taint.agree_ofRegs (vars_agree hpub h.1
      (by have := h'.1; rwa [a₁_eq' hpub] at this) h.2.1
      (by have := h'.2.1; simp only [r₀, cnt_eq hpub, a₁_eq' hpub] at this; exact this))) c₂
    (fun s h => mid_ok hP hp h) (fun s h => mid_ok hP hp' h)
  have call₂ : RelCT isa (fun s₁ s₂ => PostMid P s₀ s₁ ∧ PostMid P s₀' s₂) (call name code)
      fun s₁ s₂ => End P s₀ s₁ ∧ End P s₀' s₂ :=
    ((call_rel hf (sp := s₀.sp) fun s s' ⟨h, h'⟩ => by
      have a := h'.2
      rw [st_eq hpub, scr_eq hpub, blk₂_eq hpub, k₂_eq hpub, cnt_eq hpub, a₁_eq' hpub] at a
      exact ⟨h.2, a, h.1.sp, h'.1.sp.trans hsp.symm⟩).wp
      fun s s' h => ⟨call₂_ok hP hf hp h.1, call₂_ok hP hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have fin := rel_agree (F := End P s₀) (F' := End P s₀') (G := fun _ => True) (G' := fun _ => True)
    (VG.Arm.Taint.ofRegs vars)
    (fun s s' h h' => VG.Arm.Taint.agree_ofRegs (vars_agree hpub h.1
      (by have := h'.1; rwa [a₁_eq' hpub] at this) h.2.1
      (by have := h'.2.1; rwa [r₂_eq hpub] at this))) c₃
    (fun s h => WP.mono (end_ok hP hp h) fun _ _ => trivial)
    (fun s h => WP.mono (end_ok hP hp' h) fun _ _ => trivial)
  exact pro.seq (call₁.seq (mid.seq (call₂.seq (fin.mono (fun _ _ h => h) fun _ _ _ => trivial))))

end CT

theorem update_ct {w : Nat} {P : Params w} (hP : Ok P) {name : String} {code : Prog isa}
    (hf : CalleeOk P code) :
    ConstantTime isa (updateArm P).pre (updateArm P).pub (update (w := w) name code) :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ =>
    (update_rel hpub hP hf (pre_of h₁) (pre_of h₂) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Blake2.Arm.Stream.Update

/-! ## `finalize` -/

namespace VG.Proof.Blake2.Arm.Stream.Finalize

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (call finalizePro finalizeEnd finalize)
open VG.Proof.Blake2 (finalizeArm countArm)

/-- The pieces of `finalize` around its call pass the taint analysis. -/
theorem checks {w : Nat} {P : Params w} (hP : Ok P) :
    (∃ hc, (VG.Taint.check taint (argTaint [.r0, .r2, .r3] 8) (finalizePro (w := w)) hc).isSome = true) ∧
    (∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6]) (.block (finalizeEnd (w := w))) hc).isSome =
      true) := by
  rcases hP.w with rfl | rfl <;> exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

section CT
variable {w : Nat} {P : Params w} {s₀ s₀' : State} (hpub : (finalizeArm P).pub s₀ s₀')
include hpub

theorem finalize_rel (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code)
    (hp : Pre w s₀) (hp' : Pre w s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (finalize (w := w) name code) fun _ _ => True := by
  obtain ⟨c₁, c₂⟩ := checks hP
  have hsp : s₀.sp = s₀'.sp := hpub.1
  have hst : st s₀' = st s₀ := hpub.2.1.symm
  have hout : out s₀' = out s₀ := hpub.2.2.2.2.1.symm
  have hscr : scr s₀' = scr s₀ := hpub.2.2.2.2.2.symm
  have hcnt : cnt s₀' = cnt s₀ := by simp only [cnt, countArm, hpub.2.2.1, hpub.2.2.2.1]
  have wfA : ∀ {s : State}, Pre w s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.a_st
    · exact h.a_out
    · exact h.a_scr
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := PostPro w s₀)
    (G' := PostPro w s₀') (argTaint [.r0, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (argMem_of (j := 2) hsp hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hpub.2.1
        · exact hpub.2.2.1
        · exact hpub.2.2.2.1
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hpub.2.2.2.2.1
        · exact hpub.2.2.2.2.2) c₁
    (fun s e => by rw [e]; exact pro_ok hP hp) (fun s e => by rw [e]; exact pro_ok hP hp')
  have call₁ : RelCT isa (fun s₁ s₂ => PostPro w s₀ s₁ ∧ PostPro w s₀' s₂) (call name code)
      fun s₁ s₂ => Mid P s₀ s₁ ∧ Mid P s₀' s₂ :=
    ((call_rel hf (sp := s₀.sp) fun s s' ⟨h, h'⟩ => by
      have a := h'.2
      rw [hst, hscr, hcnt] at a
      exact ⟨h.2, a, h.1.sp, h'.1.sp.trans hsp.symm⟩).wp
      fun s s' h => ⟨call_ok' hP hf hp h.1, call_ok' hP hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have fin := rel_agree (F := Mid P s₀) (F' := Mid P s₀') (G := fun _ => True) (G' := fun _ => True)
    (VG.Arm.Taint.ofRegs [.r4, .r5, .r6])
    (fun s s' h h' => VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.r4, h'.1.r4, hst]
      · rw [h.1.r5, h'.1.r5, hscr]
      · rw [h.1.r6, h'.1.r6, hout]) c₂
    (fun s h => WP.mono (end_ok hP hp h) fun _ _ => trivial)
    (fun s h => WP.mono (end_ok hP hp' h) fun _ _ => trivial)
  exact pro.seq (call₁.seq (fin.mono (fun _ _ h => h) fun _ _ _ => trivial))

end CT

theorem finalize_ct {w : Nat} {P : Params w} (hP : Ok P) {name : String} {code : Prog isa}
    (hf : CalleeOk P code) :
    ConstantTime isa (finalizeArm P).pre (finalizeArm P).pub (finalize (w := w) name code) :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ =>
    (finalize_rel hpub hP hf (pre_of h₁) (pre_of h₂) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Blake2.Arm.Stream.Finalize
