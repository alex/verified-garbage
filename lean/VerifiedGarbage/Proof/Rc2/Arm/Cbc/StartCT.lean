import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Contract
import VerifiedGarbage.Proof.Rc2.Arm.Cbc.LoopCT

/-! # CBC's public prologue and stack argument -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def startCode : Prog isa := .seq (.block [.ldrSp .r12 0])
  (.block (Impl.Rc2.Arm.Cbc.save ++ Impl.Rc2.Arm.Cbc.setup))

structure StartPost (s s' : State) : Prop where
  pre : StepPre s' (s.gpr .r3).toNat
  key : s'.gpr .r0 = s.gpr .r0
  iv : s'.gpr .r4 = s.gpr .r1
  data : s'.gpr .r1 = s.gpr .r2
  buf : s'.gpr .r2 = stackArg s 0
  count : s'.gpr .r5 = s.gpr .r3
  flag : zeroCount s' = some (s.gpr .r3 == 0)

theorem start_ok (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa startCode s (StartPost s) := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    _ivArgs, _dataArgs, _bufArgs, keyFit, ivFit, bufFit, _spFit, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (State.addr (stackArg s 0) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [startCode]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadScratch_ok s (by
    rw [hrd, hwr]
    exact ⟨⟨stackArgAddr s 0, 4⟩, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .r12) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide)) (writes₀ 280 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  rw [g₁, g₀ .r1 (by decide)] at iv₂
  rw [g₁, g₀ .r3 (by decide)] at count₂ flag₂
  rw [g₁, g₀ .r2 (by decide)] at data₂
  rw [g₁, buf₀] at buf₂
  have key₂ := (keep₂.reg .r0 (by decide)).trans ((g₁ .r0).trans (g₀ .r0 (by decide)))
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have hp₂ : StepPre s₂ (s.gpr .r3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
  exact ⟨hp₂, key₂, iv₂, data₂, buf₂, count₂, flag₂⟩

def InitialRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (contract d).pre s₁ ∧ (contract d).pre s₂ ∧ (contract d).pub s₁ s₂

def EqArgs (s₁ s₂ : State) : Prop := ∀ r ∈ ([.r0, .r1, .r2, .r3, .r12] : List Reg), s₁.gpr r = s₂.gpr r

theorem load_trace {s s' : State} {t : List Leak} (h : Exec isa (.block [.ldrSp .r12 0]) s t s') :
    t = [.addr (State.addr s.sp)] := by
  cases h with
  | block h =>
    simp only [execBlock, isa] at h
    cases he : exec (.ldrSp .r12 0) s with
    | none => simp only [he] at h; cases h
    | some u =>
      simp only [he, Option.map_some, List.append_nil, Option.some.injEq, Prod.mk.injEq] at h
      simpa only [addrs, BitVec.add_zero, List.map_cons, List.map_nil] using h.2.symm

theorem load_ct (d : Spec.Rc2.Direction) :
    RelCT isa (InitialRel d) (.block [.ldrSp .r12 0]) EqArgs := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (stackArgAddr s₁ 0) 4 := by
    rw [hp.1.1, hp.1.2.1]
    exact ⟨⟨stackArgAddr s₁ 0, 4⟩, by simp, Region.contains_self _ _⟩
  have read₂ : InRegions (s₂.rd ++ s₂.wr) (stackArgAddr s₂ 0) 4 := by
    rw [hp.2.1.1, hp.2.1.2.1]
    exact ⟨⟨stackArgAddr s₂ 0, 4⟩, by simp, Region.contains_self _ _⟩
  obtain ⟨u₁, run₁, buf₁, keep₁⟩ := loadScratch_ok s₁ read₁
  obtain ⟨u₂, run₂, buf₂, keep₂⟩ := loadScratch_ok s₂ read₂
  obtain ⟨_, v₁, ev₁, hv₁⟩ := WP.of_runBlock (Q := fun s => s = u₁) ⟨u₁, run₁, rfl⟩
  obtain ⟨_, v₂, ev₂, hv₂⟩ := WP.of_runBlock (Q := fun s => s = u₂) ⟨u₂, run₂, rfl⟩
  have eu₁ : s₁' = u₁ := (Exec.det e₁ ev₁).2.trans hv₁
  have eu₂ : s₂' = u₂ := (Exec.det e₂ ev₂).2.trans hv₂
  obtain ⟨sp, p0, p1, p2, p3, bp⟩ := hp.2.2
  constructor
  · rw [load_trace e₁, load_trace e₂, sp]
  · rw [eu₁, eu₂]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [keep₁.reg .r0 (by decide), keep₂.reg .r0 (by decide)]; exact p0
    · rw [keep₁.reg .r1 (by decide), keep₂.reg .r1 (by decide)]; exact p1
    · rw [keep₁.reg .r2 (by decide), keep₂.reg .r2 (by decide)]; exact p2
    · rw [keep₁.reg .r3 (by decide), keep₂.reg .r3 (by decide)]; exact p3
    · rw [buf₁, buf₂]; exact bp

theorem start_ct (d : Spec.Rc2.Direction) : RelCT isa (InitialRel d) startCode MaybeRel := by
  have ct : RelCT isa (InitialRel d) startCode (fun _ _ => True) := by
    apply (load_ct d).seq
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3, .r12])
      (fun _ _ h => Taint.agree_ofRegs h)
    taint_decide
  apply (ct.wpDep (fun s₁ s₂ h => ⟨start_ok d s₁ h.1, start_ok d s₂ h.2.1⟩)).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  obtain ⟨_, p0, p1, p2, p3, bp⟩ := hp.2.2
  refine ⟨(s₁.gpr .r3).toNat, h₁.pre, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p3]; exact h₂.pre
  · intro r hr
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.key, h₂.key, p0]
    · rw [h₁.data, h₂.data, p2]
    · rw [h₁.buf, h₂.buf, bp]
    · rw [h₁.iv, h₂.iv, p1]
    · rw [h₁.count, h₂.count, p3]
  · simpa using h₁.count
  · rw [p3]; simpa using h₂.count
  · rw [h₁.flag]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  · rw [h₂.flag, p3]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h

end VG.Proof.Rc2.Arm.Cbc
