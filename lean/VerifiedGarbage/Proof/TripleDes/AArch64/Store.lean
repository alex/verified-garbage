import VerifiedGarbage.Proof.TripleDes.AArch64.BlockIO

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def packHalves : List Instr := [.lsl .x .x3 .x19 32, .logic .eor .x .x3 .x3 .x20]

theorem packHalves_ok (s : State) :
    ∃ s', runBlock isa packHalves s = some s' ∧
      s'.gpr .x3 = s.gpr .x19 <<< 32 ^^^ s.gpr .x20 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [packHalves, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show (32 : Nat) < 64 from by decide, ite_true, State.read,
      BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

theorem storeTail_ok (s : State) :
    ∃ s', runBlock isa [.rev .x3 .x10] s = some s' ∧
      s'.gpr .x3 = rev64 (s.gpr .x10) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_rev]; rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write_self, State.read, BitVec.setWidth_eq]
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

theorem final_preserves : loadKept.all (fun r =>
    (instrs finalPermutation.lit).all (fun op => dstOf op != some r)) = true := by
  decide +kernel

theorem blockStore_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .x19 = l.setWidth 64) (hr : s.gpr .x20 = r.setWidth 64) :
    ∃ s', runBlock isa blockStore s = some s' ∧
      s'.gpr .x3 = rev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ loadKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, sp₁, regs₁⟩ := packHalves_ok s
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := final_raw_ok s₁
  obtain ⟨s₃, run₃, word₃, mem₃, rd₃, wr₃, sp₃, regs₃⟩ := storeTail_ok s₂
  have hword : s₁.gpr .x3 = l ++ r := by
    rw [hl, hr] at word₁
    exact word₁.trans (packHalves_shift l r)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockStore =
      (packHalves ++ permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12) ++
      [.rev .x3 .x10] := rfl
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · exact word₃.trans (congrArg rev64 (word₂.trans
      (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) hword)))
  · intro q hq
    have hno := List.all_eq_true.mp final_preserves q hq
    have hneq : q ≠ .x3 := by revert hq; cases q <;> decide
    exact (regs₃ q hneq).trans ((regs₂ q hno).trans (regs₁ q hneq))

theorem writeData_ok (s : State) (hwrite : InRegions s.wr (s.gpr .x1) 8) :
    ∃ s', runBlock isa [.str .x .x3 .x1 0] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x1) (s.gpr .x3) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hstore := exec_str_x (t := .x3) (n := .x1) (off := 0) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hwrite)
  refine ⟨{s with mem := s.mem.writeW (s.gpr .x1) (s.gpr .x3)}, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [runBlock_cons, hstore, runStep_some, runBlock_nil, BitVec.add_zero]

end VG.Proof.TripleDes.AArch64
