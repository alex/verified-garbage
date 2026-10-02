import VerifiedGarbage.Proof.TripleDes.Arm.Bytes
import VerifiedGarbage.Proof.TripleDes.Arm.Initial
import VerifiedGarbage.Proof.TripleDes.Arm.RoundBody
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def loadKept : List Reg := [.r0, .r1, .r2, .r3]

theorem readDataWords_ok (s : State) (offset : Nat) (ho : offset + 4 < 4096)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4 * t))) 4) :
    ∃ s', runBlock isa [.ldr .r4 .r1 offset, .ldr .r5 .r1 (offset + 4),
        .rev .r4 .r4, .rev .r5 .r5] s = some s' ∧
      s'.gpr .r4 = rev (s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 offset)) 32) ∧
      s'.gpr .r5 = rev (s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4))) 32) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 offset)) 4 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using hr 0 (by decide)
  have h1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4))) 4 := by
    simpa only [Nat.mul_one] using hr 1 (by decide)
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show offset < 4096 from by omega, h0, show offset + 4 < 4096 from ho, ite_true, State.load32,
      gpr_setReg, reduceCtorEq, ite_false, rd_setReg, wr_setReg, h1,
      Option.map_some, mem_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · intro r h4 h5; simp only [gpr_setReg, h4, h5, ite_false]


theorem blockLoad_ok (s : State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hread : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .r10 = ((Spec.TripleDes.permute Spec.TripleDes.ip
        (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))))) >>> 32).setWidth 32 ∧
      s'.gpr .r11 = (Spec.TripleDes.permute Spec.TripleDes.ip
        (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))))).setWidth 32 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ loadKept, s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, hi₁, lo₁, mem₁, rd₁, wr₁, sp₁, reg₁⟩ := readDataWords_ok s 0 (by decide)
    (by simpa only [Nat.zero_add] using hread)
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := initial_raw_ok s₁
  have input : s₁.gpr .r4 ++ s₁.gpr .r5 =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))) := by
    rw [hi₁, lo₁, decodeBlock_readW]
    simp only [BitVec.add_zero, Nat.zero_add]
    rw [addr_add (by omega_using [fit])]
    rfl
  rw [input] at lo₂ hi₂
  refine ⟨s₂, ?_, hi₂, lo₂, mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · rw [blockLoad, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact sp₂.trans sp₁
  · intro r hr
    have checks : ∀ r ∈ loadKept,
        ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true := by decide +kernel
    have unused : ∀ r ∈ loadKept, r ≠ .r4 ∧ r ≠ .r5 := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr).1 (unused r hr).2)

end VG.Proof.TripleDes.Arm
