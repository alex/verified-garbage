import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Load

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def pack : List Instr := [.lsl .x .x4 .x19 28, .logic .eor .x .x4 .x4 .x20]

def tail : List Instr := [.str .x .x5 .x22 0, .addImm .x .x22 .x22 8,
  .addImm .x .x21 .x21 1, .subImm .x .x4 .x21 16]

theorem pack_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64) :
    ∃ s', runBlock isa pack s = some s' ∧
      (s'.gpr .x4).setWidth 56 = c ++ d ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [pack, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show (28 : Nat) < 64 from by decide, ite_true, State.read,
      BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hc, hd]; exact pack28_shift c d
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 j + 1 - (16 : BitVec 64)) != 0) = decide (j ≠ 15) := by decide

theorem tail_ok (s : State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .x21 = BitVec.ofNat 64 j)
    (hw : InRegions s.wr (s.gpr .x22) 8) :
    ∃ s', runBlock isa tail s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x22) (s.gpr .x5) ∧
      s'.gpr .x22 = s.gpr .x22 + 8 ∧ s'.gpr .x21 = BitVec.ofNat 64 (j + 1) ∧
      isa.eval (.nonzero .x .x4) s' = some (decide (j ≠ 15)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x4 → r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) := by
  have hstore := exec_str_x (t := .x5) (n := .x22) (off := 0) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw)
  refine ⟨_, by
    rw [tail, runBlock_cons, hstore, runStep_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show (8 : Nat) < 4096 from by decide, show (1 : Nat) < 4096 from by decide,
      show (16 : Nat) < 4096 from by decide, ite_true, State.read, BitVec.setWidth_eq,
      gpr_write, reduceCtorEq, ite_false, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, BitVec.add_zero]
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rw [hc]; exact (nextRound_values j hj).1
  · change VG.AArch64.eval (.nonzero .x .x4) _ = _
    simp only [VG.AArch64.eval, State.read, gpr_write, BitVec.setWidth_eq,
      reduceCtorEq, ite_true, ite_false, hc]
    exact congrArg some (nextRound_values j hj).2
  · simp only [rd_write]
  · simp only [wr_write]
  · intro r h4 h21 h22; simp only [gpr_write, h4, h21, h22, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .x22) ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .x22 = s.gpr .x22 + 8
  counter : s'.gpr .x21 = BitVec.ofNat 64 (j + 1)
  flag : isa.eval (.nonzero .x .x4) s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ (keyKept ++ [.x19, .x20]), s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .x19 = c.setWidth 64) (hd : s.gpr .x20 = d.setWidth 64)
    (hjreg : s.gpr .x21 = BitVec.ofNat 64 j) (hw : InRegions s.wr (s.gpr .x22) 8) :
    WP isa (.block Impl.TripleDes.AArch64.Key.storeRound) s (StorePost c d j s) := by
  have code : Impl.TripleDes.AArch64.Key.storeRound =
      (pack ++ permuteCode Spec.TripleDes.pc2 56 .x5 .x4 .x6 .x7) ++ tail := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, reg₁⟩ := pack_ok s c d hc hd
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, _, mem₂, reg₂⟩ := pc2_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [word₁] at word₂
  have checks : ∀ r ∈ (keyKept ++ [.x19, .x20, .x21, .x22]),
      ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true := by decide +kernel
  have keep₂ : ∀ r ∈ (keyKept ++ [.x19, .x20, .x21, .x22]), s₂.gpr r = s.gpr r := by
    intro r hr
    have unused : ∀ r ∈ (keyKept ++ [.x19, .x20, .x21, .x22]), r ≠ .x4 := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr))
  have counter₂ := (keep₂ .x21 (by decide)).trans hjreg
  have write₂ : InRegions s₂.wr (s₂.gpr .x22) 8 := by
    rw [wr₂, wr₁, keep₂ .x22 (by decide)]; exact hw
  obtain ⟨s₃, run₃, mem₃, ptr₃, counter₃, flag₃, rd₃, wr₃, reg₃⟩ := tail_ok s₂ j hj counter₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, counter₃, flag₃, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [mem₃, mem₂, mem₁, keep₂ .x22 (by decide), word₂]
  · rw [ptr₃, keep₂ .x22 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ (keyKept ++ [.x19, .x20]),
        r ≠ .x4 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ∈ (keyKept ++ [.x19, .x20, .x21, .x22]) := by decide
    exact (reg₃ r (incl r hr).1 (incl r hr).2.1 (incl r hr).2.2.1).trans (keep₂ r (incl r hr).2.2.2)

end VG.Proof.TripleDes.AArch64.Key
