import VerifiedGarbage.Proof.Rc2.X86.Cbc.Contract
import VerifiedGarbage.Proof.Rc2.X86.Cbc.LoopCT

namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86 VG.Impl.Rc2.X86

def startCode : Prog isa := .seq (.block [.mov .eax (.mem (memOp .esp 20))])
  (.block (Impl.Rc2.X86.Cbc.save ++ Impl.Rc2.X86.Cbc.setup))

structure StartPost (s s' : State) : Prop where
  pre : StepPre s' (arg s 3).toNat
  key : s'.gpr .ebx = arg s 0
  iv : s'.gpr .ecx = arg s 1
  data : s'.gpr .esi = arg s 2
  buf : s'.gpr .ebp = arg s 4
  count : s'.gpr .edi = arg s 3
  flag : zeroCount s' = some (arg s 3 == 0)
  sp : s'.gpr .esp = s.gpr .esp

theorem start_ok (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa startCode s (StartPost s) := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    ivArgs, dataArgs, bufArgs, retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, keyFit, ivFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (addr32 (arg s 4) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨addr32 (arg s 4), 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [startCode]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadArg_ok s .eax 4 (by
    rw [hrd, hwr, argAddr_eq s 4 (by omega)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit 4 (by decide)⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  have saveFrame : Frame [⟨addr32 (arg s 4), 512⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have args₁ := args_frame saveFrame sp₁ spFit (by simpa using bufArgs)
  have readArgs₁ (i : Nat) (hi : i < 4) : InRegions (s₁.rd ++ s₁.wr) (argAddr s₁ i) 4 := by
    have ptr : argAddr s₁ i = argAddr s i := by unfold argAddr; rw [sp₁]
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, hrd, hwr, ptr, argAddr_eq s i (by omega)]
    exact ⟨⟨argAddr s 0, 20⟩, by simp, argContains s spFit i (by omega)⟩
  obtain ⟨s₂, run₂, key₂, iv₂, data₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁ readArgs₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at iv₂
  rw [args₁ 2 (by decide)] at data₂
  rw [args₁ 3 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  have sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have hp₂ : StepPre s₂ (arg s 3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, hr, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [sp₂]; exact stackLo
    · simpa only [stackR, keyR, sp₂, key₂] using stackKey
    · simpa only [stackR, ivR, sp₂, iv₂] using stackIv
    · simpa only [stackR, dataR, sp₂, data₂] using stackData
    · simpa only [stackR, bufR, sp₂, buf₂] using stackBuf
  exact ⟨hp₂, key₂, iv₂, data₂, buf₂, count₂, flag₂, sp₂⟩

def InitialRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (contract d).pre s₁ ∧ (contract d).pre s₂ ∧ (contract d).pub s₁ s₂

def startTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 24 }

theorem startTaint_wf {d : Spec.Rc2.Direction} {s : State} (h : (contract d).pre s) : VG.X86.Taint.Wf startTaint s := by
  obtain ⟨_, wr, _, _, _, _, _, _, ai, ad, ab, ri, rd, rb, _, _, _, _, _, _, _, spfit, _⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [startTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (n := 20) (by omega) ri ai
  · exact Taint.frame_disjoint (n := 20) (by omega) rd ad
  · exact Taint.frame_disjoint (n := 20) (by omega) rb ab

theorem startTaint_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h : InitialRel d s₁ s₂) :
    VG.X86.Taint.Agree startTaint s₁ s₂ := by
  obtain ⟨h₁, h₂, sp, args⟩ := h
  have fit : ∀ s, (contract d).pre s → (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := by
    intro s hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hs
    exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    startTaint_wf h₁, startTaint_wf h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [startTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [startTaint] at hk
    rw [show Taint.depth startTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem start_ct (d : Spec.Rc2.Direction) : RelCT isa (InitialRel d) startCode MaybeRel := by
  have ct : RelCT isa (InitialRel d) startCode (fun _ _ => True) := by
    apply RelCT.taint (A := taint) startTaint (fun _ _ h => startTaint_agree h)
    taint_decide
  apply (ct.wpDep (fun s₁ s₂ h => ⟨start_ok d s₁ h.1, start_ok d s₂ h.2.1⟩)).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  obtain ⟨sp, args⟩ := hp.2.2
  have p0 := args 0 (by decide)
  have p1 := args 1 (by decide)
  have p2 := args 2 (by decide)
  have p3 := args 3 (by decide)
  have bp := args 4 (by decide)
  refine ⟨(arg s₁ 3).toNat, h₁.pre, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p3]; exact h₂.pre
  · intro r hr
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.key, h₂.key, p0]
    · rw [h₁.iv, h₂.iv, p1]
    · rw [h₁.data, h₂.data, p2]
    · rw [h₁.count, h₂.count, p3]
    · rw [h₁.buf, h₂.buf, bp]
    · rw [h₁.sp, h₂.sp, sp]
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

end VG.Proof.Rc2.X86.Cbc
