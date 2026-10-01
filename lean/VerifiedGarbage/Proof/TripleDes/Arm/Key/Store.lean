import VerifiedGarbage.Proof.TripleDes.Arm.Key.Load
import VerifiedGarbage.Proof.TripleDes.Arm.WordStore
import VerifiedGarbage.Proof.TripleDes.Arm.Word
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps

namespace VG.Proof.TripleDes.Arm.Key
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (gpr_subFlags mem_subFlags rd_subFlags wr_subFlags)

def tail : List Instr := [.str .r4 .r8 0, .str .r5 .r8 4,
  .dp .add .r8 .r8 (.imm 8), .dp .add .r9 .r9 (.imm 1), .cmp .r9 (.imm 16)]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) ∧
    (!(BitVec.ofNat 32 j + 1 - (16 : BitVec 32) == 0)) = decide (j ≠ 15) := by decide

theorem tail_ok (s : State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r9 = BitVec.ofNat 32 j)
    (fit : (s.gpr .r8).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa tail s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r8)) (s.gpr .r5 ++ s.gpr .r4) ∧
      s'.gpr .r8 = s.gpr .r8 + 8 ∧ s'.gpr .r9 = BitVec.ofNat 32 (j + 1) ∧
      isa.eval .ne s' = some (decide (j ≠ 15)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r9 → r ≠ .r8 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 0)) 4 := by
    simpa only [Nat.mul_zero] using hw 0 (by decide)
  have h1 : InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 4)) 4 := by
    simpa only [Nat.mul_one] using hw 1 (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [tail, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.store32, h0, h1, ite_true, Op2.eval, Option.map_some,
      gpr_setReg, ite_false, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_subFlags, mem_setReg, BitVec.add_zero]
    rw [addr_add (by omega_using [fit])]
    exact writeW_pair s.mem _ _ _
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
    rw [hc]; exact (nextRound_values j hj).1
  · change VG.Arm.eval .ne _ = _
    simp only [VG.Arm.eval, subFlags, hc]
    exact congrArg some (nextRound_values j hj).2
  · simp only [rd_subFlags, rd_setReg]
  · simp only [wr_subFlags, wr_setReg]
  · intro r h9 h8; simp only [gpr_subFlags, gpr_setReg, h9, h8, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (State.addr (s.gpr .r8))
    ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .r8 = s.gpr .r8 + 8
  counter : s'.gpr .r9 = BitVec.ofNat 32 (j + 1)
  flag : isa.eval .ne s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ (keyKept ++ [.r10, .r11]), s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r10 = c.setWidth 32) (hd : s.gpr .r11 = d.setWidth 32)
    (hjreg : s.gpr .r9 = BitVec.ofNat 32 j)
    (fit : (s.gpr .r8).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 (4 * t))) 4) :
    WP isa (.block Impl.TripleDes.Arm.Key.storeRound) s (StorePost c d j s) := by
  have code : Impl.TripleDes.Arm.Key.storeRound =
      permuteCode Spec.TripleDes.pc2 56 28 32 .r4 .r5 .r11 .r10 .r12 .lr ++ tail := rfl
  rw [code, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, _, mem₁, reg₁⟩ := pc2_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have input : packedInput 56 28 (s.gpr .r11) (s.gpr .r10) = c ++ d := by
    rw [hd, hc]; exact packed28 c d
  rw [input] at lo₁ hi₁
  have checks : ∀ r ∈ (keyKept ++ [.r10, .r11, .r9, .r8]),
      ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true := by decide +kernel
  have keep₁ : ∀ r ∈ (keyKept ++ [.r10, .r11, .r9, .r8]), s₁.gpr r = s.gpr r :=
    fun r hr => reg₁ r (checks r hr)
  have write₁ : ∀ t < 2, InRegions s₁.wr (State.addr (s₁.gpr .r8 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [wr₁, keep₁ .r8 (by decide)]; exact hw
  have fit₁ : (s₁.gpr .r8).toNat + 8 ≤ 2 ^ 32 := by
    rw [keep₁ .r8 (by decide)]; exact fit
  obtain ⟨s₂, run₂, mem₂, ptr₂, counter₂, flag₂, rd₂, wr₂, reg₂⟩ :=
    tail_ok s₁ j hj ((keep₁ .r9 (by decide)).trans hjreg) fit₁ write₁
  refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, ?_, counter₂, flag₂, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  · rw [mem₂, mem₁, keep₁ .r8 (by decide), lo₁, hi₁, BitVec.setWidth_eq, packed48]
  · rw [ptr₂, keep₁ .r8 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ (keyKept ++ [.r10, .r11]),
        r ≠ .r9 ∧ r ≠ .r8 ∧ r ∈ (keyKept ++ [.r10, .r11, .r9, .r8]) := by decide
    exact (reg₂ r (incl r hr).1 (incl r hr).2.1).trans (keep₁ r (incl r hr).2.2)

end VG.Proof.TripleDes.Arm.Key
