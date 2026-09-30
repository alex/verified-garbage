import VerifiedGarbage.Proof.Rc2.Arm.KeyIO
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Rc2.Arm.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # Verified RC2 key expansion -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let out : Region := ⟨State.addr (s.gpr .r3), 128⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 512⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, args] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 512 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      Spec.Rc2.validKey (s.gpr .r1).toNat (s.gpr .r2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (State.addr (s.gpr .r3)) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem key_body_correct (s : State) (hs : keyContract.pre s) :
    WP isa expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ keyContract.post s s') := by
  obtain ⟨hrd, hwr, keyOut, keyScratch, outScratch, _argsOut, _argsScratch, keyFit, outFit, scratchFit, _spFit, ht, ht', hb, hb'⟩ := hs
  have writes : ∀ i < 9, InRegions s.wr (State.addr (stackArg s 0) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [expandKey]
  apply WP.seq
  obtain ⟨s₀, run₀, scratch₀, keep₀⟩ := loadScratch_ok s (by
    rw [hrd, hwr]
    exact ⟨⟨stackArgAddr s 0, 4⟩, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have gpr₀ (r : Reg) (hr : r ≠ .r12) : s₀.gpr r = s.gpr r := keep₀.reg r (by simpa using hr)
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono (saveCode_ok s₀ .r12 savedReg 9 (by decide)
    (by rw [scratch₀]; omega) (by rw [keep₀.wr, scratch₀]; exact writes))
  intro s₁ h₁
  obtain ⟨s₂, run₂, r8₂, key₂, len₂, ptr₂, bits₂, zero₂, keep₂⟩ := pinKey_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [h₁.1, scratch₀] at r8₂
  rw [h₁.1, gpr₀ .r0 (by decide)] at key₂
  rw [h₁.1, gpr₀ .r1 (by decide)] at len₂
  rw [h₁.1, gpr₀ .r3 (by decide)] at ptr₂
  rw [h₁.1, gpr₀ .r2 (by decide)] at bits₂
  have scratchFrame : Frame [⟨State.addr (stackArg s 0), 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem, h₁.2.2.2, keep₀.mem, scratch₀]
    apply (saveMem_frame_le _ _ _ 9 64 (by decide) (by decide)).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, List.mem_cons_self,
      Region.sub_prefix (by decide)⟩
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (State.addr (s₂.gpr .r4)) (s.gpr .r1).toNat =
      Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat := by
    rw [key₂]
    exact bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega)
  have read₂ : ∀ i < (s.gpr .r1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r4) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (State.addr (s₂.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨State.addr (s.gpr .r3), 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ (s.gpr .r1).toNat ht ht' (by rw [key₂]; exact keyFit) (by rw [ptr₂]; exact outFit)
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (State.addr (s₃.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .r6 (by decide)]; exact write₂
  apply WP.mono (expandReduce_ok s₃ _ (s.gpr .r2).toNat hb hb' (by rw [h₃.1.reg .r6 (by decide), ptr₂]; exact outFit)
    (by simpa using (h₃.1.reg .r7 (by decide)).trans bits₂) write₃
    (by rw [h₃.1.reg .r6 (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨State.addr (s.gpr .r3), 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have r8₄ : s₄.gpr .r8 = stackArg s 0 := (core.reg .r8 (by decide)).trans r8₂
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (State.addr (s.gpr .r3))
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .r6 (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat).length = (s.gpr .r1).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, base₅, keep₅⟩ := scratchBase_ok s₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [r8₄] at base₅
  have rd₅ := keep₅.rd.trans rd₄
  have wr₅ := keep₅.wr.trans wr₄
  have scratchRead : ∀ i ∈ List.range 9,
      InRegions (s₅.rd ++ s₅.wr) (State.addr (s₅.gpr .r12) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [rd₅, wr₅, base₅, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have stored : ∀ i ∈ List.range 9,
      s₅.mem.readW (State.addr (s₅.gpr .r12) + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [keep₅.mem, base₅, outFrame.readW (r := ⟨State.addr (stackArg s 0), 512⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀]
    rw [saveMem_read _ _ _ 9 (by decide) i bound]
    exact gpr₀ _ (by
      have sep : ∀ i ∈ List.range 9, savedReg i ≠ .r12 := by decide
      exact sep i hi)
  rw [keyRestore_eq]
  apply WP.mono (restoreCode_ok s₅ .r12 savedReg (List.range 9) s.gpr (by rw [base₅]; omega)
    (by decide) (by decide) scratchRead stored)
  intro s₆ h₆
  constructor
  · intro r hr
    exact h₆.1 r (by
      have covered : ∀ r ∈ preserved, r ∈ (List.range 9).map savedReg := by decide
      exact covered r hr)
  · change Spec.Rc2.scheduleAt s₆.mem (State.addr (s.gpr .r3)) = _
    rw [h₆.2.mem, keep₅.mem]
    exact scheduleAt_expanded expanded

def keySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 8 | .r3 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x4001 then 0x30 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 512⟩]

theorem key_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_body_correct s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

def keyTaint : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, argLen := 4 }

theorem keyTaint_wf {s : State} (h : keyContract.pre s) : VG.Arm.Taint.Wf keyTaint s := by
  obtain ⟨_, wr, _, _, _, ao, asc, _, _, _, spfit, _⟩ := h
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spfit, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  have addr : State.addr s.sp = stackArgAddr s 0 := by simp [stackArgAddr]
  simp only [keyTaint, addr, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ao
  · exact asc

theorem keyTaint_agree {s₁ s₂ : State} (h₁ : keyContract.pre s₁) (h₂ : keyContract.pre s₂)
    (hp : keyContract.pub s₁ s₂) : VG.Arm.Taint.Agree keyTaint s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    keyTaint_wf h₁, keyTaint_wf h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · have argByte_eq (s : State) : Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
      simp [Taint.argByte, stackArgAddr]
    simp only [keyTaint] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

theorem expandKey_constantTime : ConstantTime isa keyContract.pre keyContract.pub expandKey := by
  exact VG.Taint.constantTime (A := taint) keyTaint (fun _ _ h₁ h₂ hp => keyTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem key_verified : Verified target expandKey (Spec.Rc2.expandKeyContract abi) := by
  refine Verified.of_correct key_correct expandKey_constantTime ?_
  sig_implies [Spec.Rc2.expandKeyContract, Spec.Rc2.expandKeySig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, keyContract, Spec.Rc2.validKey]
    [keySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySatState

end VG.Proof.Rc2.Arm
