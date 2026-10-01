import VerifiedGarbage.Proof.TripleDes.Arm.BlockIO
import VerifiedGarbage.Proof.TripleDes.Arm.WordStore
import VerifiedGarbage.Proof.TripleDes.Word

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

def storeTail (d : Direction) : List Instr :=
  [.rev .r4 .r4, .rev .r5 .r5, .str .r4 .r1 0, .str .r5 .r1 4,
    .dp (if d = .encrypt then .sub else .add) .r0 .r0
      (.imm (if d = .encrypt then 384 else 8))]

theorem storeTail_ok (d : Direction) (s : State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa (storeTail d) s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1))
        (byteRev64 (s.gpr .r4 ++ s.gpr .r5)) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 - 384 else s.gpr .r0 + 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 0)) 4 := by
    simpa only [Nat.mul_zero] using hw 0 (by decide)
  have h1 : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 4)) 4 := by
    simpa only [Nat.mul_one] using hw 1 (by decide)
  cases d <;> refine ⟨_, by
    simp (config := {decide := true}) only [storeTail, ite_true, ite_false,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, h0, h1,
      Op2.eval, Option.map_some, gpr_setReg, mem_setReg, wr_setReg]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false,
    rd_setReg, wr_setReg, sp_setReg]
  all_goals try
    simp only [mem_setReg, BitVec.add_zero]
    rw [addr_add (by omega_using [fit])]
    exact (writeW_pair s.mem _ _ _).trans (congrArg (s.mem.writeW _) (revPair _ _))
  all_goals
    intro r h0 h4 h5
    simp only [h0, h4, h5, ite_false]

theorem blockStore_ok (d : Direction) (s : State) (l r : BitVec 32)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa (blockStore d) s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1))
        (byteRev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r))) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 - 384 else s.gpr .r0 + 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ loadKept, q ≠ .r0 → s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, reg₁⟩ := final_raw_ok s
  rw [hl, hr] at lo₁ hi₁
  have keeps : ∀ q ∈ loadKept, s₁.gpr q = s.gpr q := by
    intro q hq
    have checks : ∀ q ∈ loadKept,
        ((instrs finalPermutation.lit).all fun op => dstOf op != some q) = true := by decide +kernel
    exact reg₁ q (checks q hq)
  have fit₁ : (s₁.gpr .r1).toNat + 8 ≤ 2 ^ 32 := by rw [keeps .r1 (by decide)]; exact fit
  have hw₁ : ∀ t < 2, InRegions s₁.wr (State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [wr₁, keeps .r1 (by decide)]; exact hw
  obtain ⟨s₂, run₂, mem₂, ptr₂, rd₂, wr₂, sp₂, reg₂⟩ := storeTail_ok d s₁ fit₁ hw₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [blockStore, ← storeTail, runBoxes_append, run₁, Option.bind_some, run₂]
  · rw [mem₂, mem₁, keeps .r1 (by decide), hi₁, lo₁, VG.Proof.TripleDes.halves_append]
  · rw [ptr₂, keeps .r0 (by decide)]
  · intro q hq h0
    have unused : ∀ q ∈ loadKept, q ≠ .r4 ∧ q ≠ .r5 := by decide
    exact (reg₂ q h0 (unused q hq).1 (unused q hq).2).trans (keeps q hq)

end VG.Proof.TripleDes.Arm
