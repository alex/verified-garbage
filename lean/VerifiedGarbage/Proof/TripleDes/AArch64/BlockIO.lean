import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.TripleDes.AArch64.Initial
import VerifiedGarbage.Proof.TripleDes.AArch64.Word
import VerifiedGarbage.Proof.TripleDes.AArch64.Box
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def loadKept : List Reg := [.x0, .x1, .x2, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem readData_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8) :
    ∃ s', runBlock isa [.ldr .x .x3 .x1 0, .rev .x3 .x3] s = some s' ∧
      s'.gpr .x3 = Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .x1)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → s'.gpr r = s.gpr r) := by
  have hload := exec_ldr_x (t := .x3) (n := .x1) (off := 0) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hread)
  refine ⟨_, by
    simp only [runBlock_cons, hload, runStep_some, runBlock_nil, exec_rev, State.read,
      BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
    exact (decodeBlock_readW s.mem (s.gpr .x1)).symm
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

def splitHalves : List Instr :=
  [.lsr .x .x19 .x10 32, rr .x20 .x10] ++ mask .x20 32

theorem splitHalves_ok (s : State) :
    ∃ s', runBlock isa splitHalves s = some s' ∧
      s'.gpr .x19 = s.gpr .x10 >>> 32 ∧
      s'.gpr .x20 = ((s.gpr .x10).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [splitHalves, mask, rr, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, Size.bits,
      show (32 : Nat) < 64 from by decide, show (0 : Nat) < 4096 from by decide,
      ite_true, State.read, gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    exact mask_word _ 32 (by decide) (by decide)
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r h19 h20; simp only [gpr_write, h19, h20, ite_false]

theorem upperHalf_extend (x : BitVec 64) :
    x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, hj, decide_true, Bool.true_and]
  · have hz : x.getLsbD (32 + j) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp only [h, hj, decide_false, decide_true, Bool.false_and, Bool.true_and, hz]

theorem runAppend_some (xs ys : List Instr) (s t u : State)
    (hx : runBlock isa xs s = some t) (hy : runBlock isa ys t = some u) :
    runBlock isa (xs ++ ys) s = some u := by
  calc
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) :=
      runBoxes_append xs ys s
    _ = (some t).bind (runBlock isa ys) := congrArg (fun v => v.bind (runBlock isa ys)) hx
    _ = runBlock isa ys t := Option.bind_some t (runBlock isa ys)
    _ = some u := hy


theorem initial_preserves : loadKept.all (fun r =>
    (instrs initialPermutation.lit).all (fun op => dstOf op != some r)) = true := by
  decide +kernel

theorem blockLoad_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .x19 =
        (((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .x1)))) >>> 32).setWidth 32).setWidth 64 ∧
      s'.gpr .x20 =
        ((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .x1)))).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ loadKept, s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, sp₁, regs₁⟩ := readData_ok s hread
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := initial_raw_ok s₁
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, sp₃, regs₃⟩ := splitHalves_ok s₂
  have hword : s₂.gpr .x10 = Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .x1))) :=
    word₂.trans (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) word₁)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockLoad =
      (([.ldr .x .x3 .x1 0, .rev .x3 .x3] : List Instr) ++
        permuteCode Spec.TripleDes.ip 64 .x10 .x3 .x11 .x12) ++ splitHalves := by
    simp only [blockLoad, splitHalves, List.append_assoc]
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · exact left₃.trans ((congrArg (fun x : BitVec 64 => x >>> 32) hword).trans (upperHalf_extend _))
  · exact right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hword)
  · intro r hr
    have hno := List.all_eq_true.mp initial_preserves r hr
    have hne : r ≠ .x3 ∧ r ≠ .x19 ∧ r ≠ .x20 := by revert hr; cases r <;> decide
    exact (regs₃ r hne.2.1 hne.2.2).trans ((regs₂ r hno).trans (regs₁ r hne.1))

end VG.Proof.TripleDes.AArch64
