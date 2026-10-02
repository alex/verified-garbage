import VerifiedGarbage.Proof.TripleDes.X86.Key.Load
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Proof.TripleDes.X86.Word

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86

def storeMem (s : State) : Mem :=
  (((s.mem.writeW (wordAddr (roundKeyPtr s) 0) (s.gpr .eax)).writeW
    (wordAddr (roundKeyPtr s) 1) (s.gpr .ebx)).writeW
    (wordAddr (s.gpr .ebp) 4) (roundKeyPtr s + 8)).writeW
    (wordAddr (s.gpr .ebp) 5) (roundCount s + 1)

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) ∧
    (!(BitVec.ofNat 32 j + 1 - (16 : BitVec 32) == 0)) = decide (j ≠ 15) := by decide

theorem tail_ok (s : State) (hok : Ok sboxCfg s)
    (hw : ∀ t < 2, InRegions s.wr (wordAddr (roundKeyPtr s) t) 4)
    :
    ∃ s', runBlock isa Impl.TripleDes.X86.Key.storeTail s = some s' ∧
      s'.mem = storeMem s ∧ s'.zf = some ((roundCount s + 1 - 16) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) := by
  have hw4 := hok.slotIn 4 (by decide)
  have hw5 := hok.slotIn 5 (by decide)
  have hr4 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 := by
    obtain ⟨r, h, hc⟩ := hw4; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hr5 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 5) 4 := by
    obtain ⟨r, h, hc⟩ := hw5; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hw0 := hw 0 (by decide)
  have hw1 := hw 1 (by decide)
  simp only [wordAddr, addr, sboxCfg, roundKeyPtr] at hw4 hw5 hr4 hr5 hw0 hw1
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Key.storeTail, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.load32, State.store32, State.ea, memOp,
      hw4, hw5, hr4, hr5, hw0, hw1, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [mem_setReg, mem_arithFlags, storeMem, roundKeyPtr, roundCount,
    wordAddr, addr, gpr_setReg, gpr_arithFlags, rd_setReg, wr_setReg,
    rd_arithFlags, wr_arithFlags, zf_setReg, zf_arithFlags]
  all_goals try rfl
  all_goals
    intro r hc hd
    simp only [hc, hd, ite_false]

def keyStoreMem (s : State) (k : BitVec 64) : Mem :=
  ((s.mem.writeW (wordAddr (roundKeyPtr s) 0) k).writeW
    (wordAddr (s.gpr .ebp) 4) (roundKeyPtr s + 8)).writeW
    (wordAddr (s.gpr .ebp) 5) (roundCount s + 1)

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = keyStoreMem s ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : roundKeyPtr s' = roundKeyPtr s + 8
  counter : roundCount s' = BitVec.ofNat 32 (j + 1)
  flag : isa.eval .ne s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .esi = c.setWidth 32) (hd : s.gpr .edi = d.setWidth 32)
    (hcount : roundCount s = BitVec.ofNat 32 j) (hok : Ok sboxCfg s)
    (fit : (roundKeyPtr s).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (wordAddr (roundKeyPtr s) t) 4)
    :
    WP isa (.block Impl.TripleDes.X86.Key.storeRound) s (StorePost c d j s) := by
  rw [Impl.TripleDes.X86.Key.storeRound, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, reg₁⟩ := pc2_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have input : packedInput 56 28 (s.gpr .edi) (s.gpr .esi) = c ++ d := by
    rw [hd, hc]; exact packed28 c d
  rw [input] at lo₁ hi₁
  have checks : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp],
      ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true := by decide +kernel
  have keep₁ : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s₁.gpr r = s.gpr r :=
    fun r hr => reg₁ r (checks r hr)
  have base₁ := keep₁ .ebp (by decide)
  have ptr₁ : roundKeyPtr s₁ = roundKeyPtr s := by unfold roundKeyPtr; rw [base₁, mem₁]
  have count₁ : roundCount s₁ = roundCount s := by unfold roundCount; rw [base₁, mem₁]
  have hok₁ : Ok sboxCfg s₁ := hok.congr base₁ base₁ rd₁ wr₁
  have hw₁ : ∀ t < 2, InRegions s₁.wr (wordAddr (roundKeyPtr s₁) t) 4 := by
    rw [wr₁, ptr₁]; exact hw
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, reg₂⟩ := tail_ok s₁ hok₁ hw₁
  have regs : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], s₂.gpr r = s.gpr r := by
    intro r hr
    have diffs : ∀ r ∈ [Reg.esi, .edi, .esp, .ebp], r ≠ .ecx ∧ r ≠ .edx := by decide
    exact (reg₂ r (diffs r hr).1 (diffs r hr).2).trans (keep₁ r hr)
  have hm : s₂.mem = keyStoreMem s ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64) := by
    rw [mem₂, storeMem, ptr₁, count₁, base₁, mem₁, lo₁, hi₁, BitVec.setWidth_eq]
    have ha : wordAddr (roundKeyPtr s) 1 = wordAddr (roundKeyPtr s) 0 + 4 := by
      rw [show wordAddr (roundKeyPtr s) 0 = (roundKeyPtr s).setWidth 64 from by
        simp [wordAddr, addr]]
      exact VG.X86.addr_eq (x := roundKeyPtr s) (k := 4) (by omega)
    rw [ha, writeW_pair, packed48]
    rfl
  refine WP.of_runBlock ⟨s₂, run₂, ⟨hm, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, regs⟩⟩
  · unfold roundKeyPtr
    rw [regs .ebp (by decide), hm, keyStoreMem,
      Mem.readW_writeW_sep (fun a h4 h5 => counter_ptr_sep s hok.fit a h5 h4) (by decide),
      Mem.readW_writeW_self32]
    rfl
  · unfold roundCount
    rw [regs .ebp (by decide), hm, keyStoreMem, Mem.readW_writeW_self32, hcount]
    exact (nextRound_values j hj).1
  · change s₂.zf.map (!·) = _
    rw [flag₂, count₁, hcount, Option.map_some]
    exact congrArg some (nextRound_values j hj).2

end VG.Proof.TripleDes.X86.Key
