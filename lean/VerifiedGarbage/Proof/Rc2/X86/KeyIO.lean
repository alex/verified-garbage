import VerifiedGarbage.Proof.Rc2.X86.KeyBody
import VerifiedGarbage.Proof.Rc2.X86.Save
import VerifiedGarbage.TCB.X86.Target

/-! # Stack arguments and callee saves for RC2 key expansion -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

def savedReg (i : Nat) : Reg := saved.getD i .eax

theorem keySave_eq : save = saveCode .eax savedReg 4 := rfl

theorem keyRestore_eq : restore = restoreCode .eax savedReg (List.range 4) := rfl

theorem argAddr_eq (s : State) (i : Nat) (fit : (s.gpr .esp).toNat + 4 + 4 * i < 2 ^ 32) :
    argAddr s i = addr32 (s.gpr .esp) + BitVec.ofNat 64 (4 + 4 * i) :=
  addr_add (by omega)

theorem argContains (s : State) (fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32)
    (i : Nat) (hi : i < 5) :
    (Region.mk (argAddr s 0) 20).Contains
      (addr32 (s.gpr .esp) + BitVec.ofNat 64 (4 + 4 * i)) 4 := by
  rw [argAddr_eq s 0 (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by decide)

theorem args_frame {s s' : State} {rs : List Region}
    (frame : Frame rs s.mem s'.mem) (sp : s'.gpr .esp = s.gpr .esp)
    (fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32)
    (sep : ∀ r ∈ rs, (Region.mk (argAddr s 0) 20).Disjoint r) :
    ∀ i < 5, arg s' i = arg s i := by
  intro i hi
  unfold arg
  have e : argAddr s' i = argAddr s i := by unfold argAddr; rw [sp]
  rw [e, argAddr_eq s i (by omega)]
  exact frame.readW (argContains s fit i hi) sep (by decide)

theorem loadArg_ok (s : State) (r : Reg) (i : Nat)
    (readable : InRegions (s.rd ++ s.wr) (argAddr s i) 4) :
    ∃ s', runBlock isa [.mov r (.mem (memOp .esp (4 + 4 * i)))] s = some s' ∧
      s'.gpr r = arg s i ∧ Keep [r] s s' := by
  simp only [argAddr] at readable
  refine ⟨s.setReg r (arg s i), ?_, gpr_setReg_self _ _ _, ?_⟩
  · simp only [runBlock_cons, exec, readSrc, State.ea, memOp, State.load32,
      readable, ite_true, Option.map_some, runStep_some, runBlock_nil]
    rfl
  · exact ⟨fun _ hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem arg_keep {s s' : State} {rs : List Reg} (keep : Keep rs s s')
    (hsp : .esp ∉ rs) (i : Nat) : arg s' i = arg s i := by
  unfold arg argAddr
  rw [keep.mem, keep.reg .esp hsp]

theorem pinKey_ok (s : State)
    (readable : ∀ i < 5, InRegions (s.rd ++ s.wr) (argAddr s i) 4) :
    WP isa (.block [.mov .ebp (.mem (memOp .esp 4)), .mov .esi (.mem (memOp .esp 8)),
      .mov .edi (.mem (memOp .esp 16)), imm .ecx 0]) s (fun s' =>
      s'.gpr .ebp = arg s 0 ∧ s'.gpr .esi = arg s 1 ∧ s'.gpr .edi = arg s 3 ∧
      s'.gpr .ecx = 0 ∧ Keep [.ebp, .esi, .edi, .ecx] s s') := by
  have r0 := readable 0 (by decide)
  have r1 := readable 1 (by decide)
  have r3 := readable 3 (by decide)
  simp only [argAddr, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at r0 r1 r3
  refine WP.of_runBlock ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, exec, imm, memOp, State.ea,
      readSrc, State.load32, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      r0, r1, r3, ite_true, ite_false, Option.map_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem bytesAt_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  unfold Spec.Rc2.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Rc2.X86
