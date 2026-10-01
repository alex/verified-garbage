import VerifiedGarbage.Proof.Rc2.X86_64.Sse2PiLookup
import VerifiedGarbage.Impl.Rc2.X86_64.ExpandKey
import VerifiedGarbage.Proof.Rc2.X86_64.Save
import VerifiedGarbage.Proof.Rc2.Expansion

/-! # Individual steps of RC2 key expansion -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

def keyTemps : List Reg := [.rax, .rbx, .rcx, .r9, .r10, .r11]

theorem copyKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .r12 + s.gpr .rbx) 1)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    ∃ s', runBlock isa copyKey s = some s' ∧
      s'.gpr .rbx = s.gpr .rbx + 1 ∧
      s'.zf = some ((s.gpr .rbx + 1 - s.gpr .r13) == 0) ∧
      Keep keyTemps
        {s with mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx) (s.mem (s.gpr .r12 + s.gpr .rbx))} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [copyKey, indexed, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load8, State.store8, State.ea,
      BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_zero,
      Option.map_some, Option.bind_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg,
      wr_setReg, readable, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg_self]
    rfl
  · exact zf_arithFlags _ _ _ _
  · constructor
    · intro r hr
      simp only [keyTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_arithFlags, gpr_setReg, hr.1, hr.2.1, ite_false]
    · simp only [mem_arithFlags, mem_setReg, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
        BitVec.setWidth_eq]
    · simp only [rd_arithFlags, rd_setReg]
    · simp only [wr_arithFlags, wr_setReg]

theorem add_minus_one (a : BitVec 64) : a + BitVec.ofInt 64 (-1) = a - 1 := by
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem fillInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .r14 + s.gpr .rbx - 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - s.gpr .r13)) 1) :
    ∃ s', runBlock isa
      [.movzx8 .rax (indexed .r14 .rbx (-1)), rr .r9 .rbx, .alu .sub .r9 (.reg .r13),
       .movzx8 .rcx (indexed .r14 .r9), .alu .add .rax (.reg .rcx)] s = some s' ∧
      s'.gpr .rax = (s.mem (s.gpr .r14 + s.gpr .rbx - 1#64)).setWidth 64 +
        (s.mem (s.gpr .r14 + (s.gpr .rbx - s.gpr .r13))).setWidth 64 ∧
      Keep [.rax, .rcx, .r9] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [indexed, rr, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load8, State.ea,
      BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_zero,
      Option.map_some, Option.bind_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      add_minus_one, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem fillOutput_ok (s : State)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    ∃ s', runBlock isa [.store8 (indexed .r14 .rbx) .rax,
      .alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 128)] s = some s' ∧
      s'.gpr .rbx = s.gpr .rbx + 1 ∧
      s'.zf = some ((s.gpr .rbx + 1 - 128) == 0) ∧
      Keep keyTemps {s with mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx) ((s.gpr .rax).setWidth 8)} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [indexed, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.store8, State.ea,
      BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_zero,
      Option.bind_some, gpr_setReg, writable, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg_self]
    rfl
  · exact zf_arithFlags _ _ _ _
  · constructor
    · intro r hr
      simp only [keyTemps, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_arithFlags, gpr_setReg, hr.2.1, ite_false]
    · simp only [mem_arithFlags, mem_setReg]
    · simp only [rd_arithFlags, rd_setReg]
    · simp only [wr_arithFlags, wr_setReg]

theorem fillKey_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .r14 + s.gpr .rbx - 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - s.gpr .r13)) 1)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    WP isa (.block fillKey) s (fun s' =>
      s'.gpr .rbx = s.gpr .rbx + 1 ∧
      s'.zf = some ((s.gpr .rbx + 1 - 128) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx)
          (Spec.Rc2.pi (s.mem (s.gpr .r14 + s.gpr .rbx - 1#64) +
          s.mem (s.gpr .r14 + (s.gpr .rbx - s.gpr .r13))))} s') := by
  rw [fillKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := fillInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (Sse2.piLookup_ok s₁ (by
    rw [keep₁.wr, keep₁.reg .r8 (by decide)]; exact hlookup))
  intro s₂ h₂
  have k₁ : Keep keyTemps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h <;> subst r <;> decide)
  have k₂ : Keep keyTemps s₁ s₂ := h₂.2.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have keep := k₁.trans k₂
  have ptr := keep.reg .r14 (by decide)
  have index := (keep₁.reg .rbx (by decide)).trans rfl
  have index₂ : s₂.gpr .rbx = s.gpr .rbx := (h₂.2.reg .rbx (by decide)).trans index
  have write₂ : InRegions s₂.wr (s₂.gpr .r14 + s₂.gpr .rbx) 1 := by
    rw [keep.wr, ptr, index₂]; exact writable
  obtain ⟨s₃, run₃, out₃, flag₃, keep₃⟩ := fillOutput_ok s₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [out₃, index₂], by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact (keep₃.reg r hr).trans (keep.reg r hr)
  · rw [keep₃.mem, keep.mem, ptr, index₂, h₂.1, out₁]
    simp [BitVec.setWidth_add]
  · exact keep₃.rd.trans keep.rd
  · exact keep₃.wr.trans keep.wr

theorem reduceInput_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .r14 + s.gpr .rbx) 1) :
    ∃ s', runBlock isa [.movzx8 .rax (indexed .r14 .rbx), .alu .and .rax (.reg .rdx)] s = some s' ∧
      s'.gpr .rax = (s.mem (s.gpr .r14 + s.gpr .rbx)).setWidth 64 &&& s.gpr .rdx ∧
      Keep [.rax] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [indexed, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.load8, State.ea, BitVec.ofInt_ofNat,
      BitVec.mul_one, BitVec.add_zero, Option.map_some, Option.bind_some, gpr_setReg,
      readable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem storeByte_ok (s : State)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    runBlock isa [.store8 (indexed .r14 .rbx) .rax] s =
      some {s with mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx) ((s.gpr .rax).setWidth 8)} := by
  simp only [indexed, runBlock_cons, runStep_some, runBlock_nil, exec, State.store8, State.ea,
    BitVec.ofInt_ofNat, BitVec.mul_one, BitVec.add_zero, writable, ite_true]

theorem descendInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - 1#64) + 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - 1#64 + s.gpr .rbp)) 1) :
    ∃ s', runBlock isa
      [.alu .sub .rbx (.imm 1), .movzx8 .rax (indexed .r14 .rbx 1), rr .r9 .rbx,
       .alu .add .r9 (.reg .rbp), .movzx8 .rcx (indexed .r14 .r9), .alu .xor .rax (.reg .rcx)] s = some s' ∧
      s'.gpr .rbx = s.gpr .rbx - 1 ∧
      s'.gpr .rax = (s.mem (s.gpr .r14 + (s.gpr .rbx - 1#64) + 1#64)).setWidth 64 ^^^
        (s.mem (s.gpr .r14 + (s.gpr .rbx - 1#64 + s.gpr .rbp))).setWidth 64 ∧
      Keep [.rax, .rbx, .rcx, .r9] s s' := by
  have one : (1#32).signExtend 64 = 1#64 := by decide
  refine ⟨_, by
    simp (config := {decide := true}) only [indexed, rr, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load8, State.ea,
      BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_zero, one,
      Option.map_some, Option.bind_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rfl
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem piStore_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    WP isa (.block (Sse2.piLookup ++ ([.store8 (indexed .r14 .rbx) .rax] : List Instr))) s (fun s' =>
      s'.gpr .rbx = s.gpr .rbx ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx) (Spec.Rc2.pi ((s.gpr .rax).setWidth 8))} s') := by
  rw [WP.block_append_iff]
  apply WP.mono (Sse2.piLookup_ok s hlookup)
  intro s₁ h₁
  have ptr := h₁.2.reg .r14 (by decide)
  have index := h₁.2.reg .rbx (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .r14 + s₁.gpr .rbx) 1 := by
    rw [h₁.2.wr, ptr, index]; exact writable
  refine WP.of_runBlock ⟨_, storeByte_ok s₁ valid, ?_⟩
  refine ⟨index, ?_⟩
  constructor
  · intro r hr
    exact h₁.2.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> subst r <;> decide))
  · change s₁.mem.writeW _ _ = _
    rw [h₁.2.mem, ptr, index, h₁.1]
    simp
  · exact h₁.2.rd
  · exact h₁.2.wr

theorem reduceKey_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .r14 + s.gpr .rbx) 1)
    (writable : InRegions s.wr (s.gpr .r14 + s.gpr .rbx) 1) :
    WP isa (.block reduceKey) s (fun s' => s'.gpr .rbx = s.gpr .rbx ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .r14 + s.gpr .rbx)
          (Spec.Rc2.pi (s.mem (s.gpr .r14 + s.gpr .rbx) &&& (s.gpr .rdx).setWidth 8))} s') := by
  rw [reduceKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := reduceInput_ok s readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .r14 (by decide)
  have index := keep₁.reg .rbx (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .r14 + s₁.gpr .rbx) 1 := by
    rw [keep₁.wr, ptr, index]; exact writable
  apply WP.mono (piStore_ok s₁ (by
    rw [keep₁.wr, keep₁.reg .r8 (by decide)]; exact hlookup) valid)
  intro s₂ h₂
  refine ⟨h₂.1.trans index, ?_⟩
  constructor
  · intro r hr
    exact (h₂.2.reg r hr).trans (keep₁.reg r (by
      simp only [List.mem_singleton]
      exact fun he => hr (he ▸ List.mem_cons_self)))
  · rw [h₂.2.mem, keep₁.mem, ptr, index, out₁]
    simp
  · exact h₂.2.rd.trans keep₁.rd
  · exact h₂.2.wr.trans keep₁.wr

theorem cmpZero_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .rbx (.imm 0)] s = some s' ∧
      s'.zf = some (s.gpr .rbx == 0) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  constructor
  · rw [zf_arithFlags]
    change some ((s.gpr .rbx - 0#64) == 0#64) = some (s.gpr .rbx == 0#64)
    rw [BitVec.sub_zero]
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem descendKey_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - 1#64) + 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .r14 + (s.gpr .rbx - 1#64 + s.gpr .rbp)) 1)
    (writable : InRegions s.wr (s.gpr .r14 + (s.gpr .rbx - 1#64)) 1) :
    WP isa (.block descendKey) s (fun s' =>
      s'.gpr .rbx = s.gpr .rbx - 1 ∧ s'.zf = some ((s.gpr .rbx - 1) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .r14 + (s.gpr .rbx - 1#64))
          (Spec.Rc2.pi (s.mem (s.gpr .r14 + (s.gpr .rbx - 1#64) + 1#64) ^^^
            s.mem (s.gpr .r14 + (s.gpr .rbx - 1#64 + s.gpr .rbp))))} s') := by
  rw [descendKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, index₁, out₁, keep₁⟩ := descendInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .r14 (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .r14 + s₁.gpr .rbx) 1 := by
    rw [keep₁.wr, ptr, index₁]; exact writable
  have split : Sse2.piLookup ++ [.store8 (indexed .r14 .rbx) .rax, .alu .cmp .rbx (.imm 0)] =
      (Sse2.piLookup ++ ([.store8 (indexed .r14 .rbx) .rax] : List Instr)) ++ [.alu .cmp .rbx (.imm 0)] := by
    rw [List.append_assoc]; rfl
  rw [split, WP.block_append_iff]
  apply WP.mono (piStore_ok s₁ (by
    rw [keep₁.wr, keep₁.reg .r8 (by decide)]; exact hlookup) valid)
  intro s₂ h₂
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpZero_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have index₂ := h₂.1.trans index₁
  refine ⟨(keep₃.reg .rbx (by decide)).trans index₂, by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact ((keep₃.reg r (by simp)).trans (h₂.2.reg r hr)).trans (keep₁.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> subst r <;> decide)))
  · rw [keep₃.mem, h₂.2.mem, keep₁.mem, ptr, index₁, out₁]
    simp
  · exact keep₃.rd.trans (h₂.2.rd.trans keep₁.rd)
  · exact keep₃.wr.trans (h₂.2.wr.trans keep₁.wr)

end VG.Proof.Rc2.X86_64
