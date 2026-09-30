import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# x86-64: code that restores MXCSR

Untrusted: everything here is checked by Lean.

Code that loads MXCSR (for Intel's MCDT prologue: see "MCDT" in
`TCB/X86_64/Isa.lean`) keeps its control bits if it first saves MXCSR in
`r11` (`mxcsrSave`), never writes `r11`, and loads it back from `r11` last
(`mxcsrRestore`). `ctlOk` checks that every load of MXCSR by some code, and
by the functions it calls, is between such a pair, and `abiPreserved_of_ctl`
extends `abiPreserved_of_exec` to such code, whatever MXCSR held on entry.
-/

namespace VG.X86_64

/-- `stmxcsr [m]; mov r11d, [m]; and r11d, 0xFFFF`: MXCSR, but for its
reserved bits, in `r11`. -/
def mxcsrSave (m : MemOp) : List Instr :=
  [.stmxcsr m, .mov32 .r11 (.mem m), .alu32 .and .r11 (.imm 0xFFFF)]

/-- `mov [m], r11d; ldmxcsr [m]`: MXCSR from `r11`. -/
def mxcsrRestore (m : MemOp) : List Instr := [.store32 m .r11, .ldmxcsr m]

/-- The operand of a block that may be `mxcsrSave`. -/
def saveOp : List Instr → Option MemOp
  | .stmxcsr m :: _ => some m
  | _ => none

/-- The operand of a block that may be `mxcsrRestore`. -/
def restoreOp : List Instr → Option MemOp
  | .store32 m _ :: _ => some m
  | _ => none

/-- Whether `.seq a b` is `mxcsrSave m`, then code that never writes `r11`,
then `mxcsrRestore m'`. -/
def restores (a b : Prog isa) : Bool :=
  match a, b with
  | .block is, .seq mid (.block js) =>
    match saveOp is, restoreOp js with
    | some m, some m' =>
      is == mxcsrSave m && js == mxcsrRestore m' && mid.allInstrs fun i => !Taint.clobbers i .r11
    | _, _ => false
  | _, _ => false

/-- Whether every load of MXCSR by `c`, and by the functions it calls, is
between `mxcsrSave` and `mxcsrRestore` (`restores`). -/
def ctlOk : Prog isa → Bool
  | .block is => is.all fun i => !loadsMxcsr i
  | .seq a b => restores a b || (ctlOk a && ctlOk b)
  | .ite _ t e => ctlOk t && ctlOk e
  | .loop b _ => ctlOk b
  | .call _ b => ctlOk b
  | .frame i b j => !loadsMxcsr i && ctlOk b && !loadsMxcsr j

/-- MXCSR's control bits, which the calling convention preserves. -/
abbrev ctl (v : BitVec 32) : BitVec 10 := v.extractLsb' 6 10

theorem restores_eq {a b : Prog isa} (h : restores a b = true) :
    ∃ m m' mid, a = .block (mxcsrSave m) ∧ b = .seq mid (.block (mxcsrRestore m')) ∧
      ∀ i ∈ instrs mid, Taint.clobbers i .r11 = false := by
  unfold restores at h
  split at h
  · split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hm⟩ := h
      refine ⟨_, _, _, rfl, rfl, fun i hi => ?_⟩
      rw [Code.allInstrs_eq, List.all_eq_true] at hm
      simpa using hm i hi
    · cases h
  · cases h

theorem ea_writeMem (s : State) (x : Mem) (m : MemOp) : ({ s with mem := x } : State).ea m = s.ea m := rfl

theorem save_exec {m : MemOp} {s s' : State} {t : List Leak}
    (h : execBlock isa (mxcsrSave m) s = some (s', t)) :
    s'.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ s'.mxcsr = s.mxcsr := by
  simp only [mxcsrSave, execBlock, isa, exec, State.store32] at h
  by_cases hw : InRegions s.wr (s.ea m) 4
  · have hl : InRegions (s.rd ++ s.wr) (s.ea m) 4 :=
      let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
    simp only [hw, ite_true, readSrc32, State.load32, ea_writeMem, hl, Option.map_some,
      Mem.readW_writeW_self32, execAlu32, Option.bind_some, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨?_, rfl⟩
    simp only [State.setReg32, State.setReg, ↓reduceIte,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
  · simp only [hw, ite_false, reduceCtorEq] at h

theorem restore_exec {m : MemOp} {s s' : State} {t : List Leak}
    (h : execBlock isa (mxcsrRestore m) s = some (s', t)) : s'.mxcsr = (s.gpr .r11).setWidth 32 := by
  simp only [mxcsrRestore, execBlock, isa, exec, State.store32] at h
  by_cases hw : InRegions s.wr (s.ea m) 4
  · have hl : InRegions (s.rd ++ s.wr) (s.ea m) 4 :=
      let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
    simp only [hw, ite_true, State.load32, ea_writeMem, hl, Mem.readW_writeW_self32,
      Option.bind_some] at h
    by_cases hz : BitVec.extractLsb' 16 16 (BitVec.setWidth 32 (s.gpr Reg.r11)) = 0
    · simp only [hz, ite_true, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl
    · simp only [hz, ite_false, Option.map_none, reduceCtorEq] at h
  · simp only [hw, ite_false, reduceCtorEq] at h

theorem ctl_and (v : BitVec 32) : ctl (BitVec.setWidth 32 (BitVec.setWidth 64 (v &&& 0xFFFF))) = ctl v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi, decide_true,
    Bool.true_and]
  rw [decide_eq_true (by omega), decide_eq_true (by omega), Bool.true_and,
    show (0xFFFF : BitVec 32).getLsbD (6 + i) = true by revert i; decide, Bool.and_true, Bool.true_and]

theorem execBlock_ctl {is : List Instr} (hc : (is.all fun i => !loadsMxcsr i) = true)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.mxcsr = s.mxcsr :=
  execBlock_mxcsr (fun i hi => by simpa using List.all_eq_true.mp hc i hi) h

/-- Code that `ctlOk` accepts keeps MXCSR's control bits. -/
theorem Exec.ctl {c : Prog isa} (hc : ctlOk c = true) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : ctl s'.mxcsr = ctl s.mxcsr := by
  induction h with
  | block h => rw [execBlock_ctl hc h]
  | seq h₁ h₂ ih₁ ih₂ =>
    simp only [ctlOk, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hr | ⟨ha, hb⟩
    · obtain ⟨m, m', mid, rfl, rfl, hk⟩ := restores_eq hr
      rw [Exec.block_iff] at h₁
      cases h₂ with
      | seq hm hr' =>
        rw [Exec.block_iff] at hr'
        rw [restore_exec hr', Exec.gpr hk hm, (save_exec h₁).1, ctl_and]
    · rw [ih₂ hb, ih₁ ha]
  | iteT _ _ ih =>
    simp only [ctlOk, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih =>
    simp only [ctlOk, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]
  | frame hp _ hq ih =>
    simp only [ctlOk, Bool.and_eq_true] at hc
    rw [pop_mxcsr hq, ih hc.1.2, push_mxcsr hp]
  | call hc₁ _ hr ih =>
    simp only [isa, call, Option.some.injEq] at hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    subst hc₁
    exact ih hc

/-- The calling-convention obligations of code that `ctlOk` accepts, from
the others. -/
theorem abiPreserved_of_ctl {c : Prog isa} (hc : ctlOk c = true) {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') (h : gprPreserved s s') : abiPreserved s s' :=
  ⟨h.1, h.2, Exec.ctl hc he⟩

end VG.X86_64
