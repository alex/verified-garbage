import VerifiedGarbage.Proof.TripleDes.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

def savedKeyAddr (s : State) : Addr := s.gpr .rdx + BitVec.ofNat 64 48

def passOffset (component : Nat) (direction : Direction) : Nat :=
  128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_signExtend (component : Nat) (hc : component < 3) (direction : Direction) :
    (BitVec.ofNat 32 (passOffset component direction)).signExtend 64 =
      BitVec.ofNat 64 (passOffset component direction) := by
  have h : ∀ c < 3,
      ((BitVec.ofNat 32 (passOffset c .encrypt)).signExtend 64 =
        BitVec.ofNat 64 (passOffset c .encrypt)) ∧
      ((BitVec.ofNat 32 (passOffset c .decrypt)).signExtend 64 =
        BitVec.ofNat 64 (passOffset c .decrypt)) := by decide +kernel
  cases direction
  · exact (h component hc).1
  · exact (h component hc).2

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) (hread : InRegions (s.rd ++ s.wr) (savedKeyAddr s) 8)
    (hwrite : InRegions s.wr (countAddr s) 8) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr .rdi = s.mem.readW (savedKeyAddr s) 64 +
        BitVec.ofNat 64 (passOffset component direction) ∧
      s'.mem = s.mem.writeW (countAddr s) (BitVec.ofNat 64 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → s'.gpr r = s.gpr r) := by
  unfold savedKeyAddr at hread
  unfold countAddr at hwrite
  have h48 : BitVec.ofInt 64 (Int.ofNat 48) = BitVec.ofNat 64 48 := rfl
  have h56 : BitVec.ofInt 64 (Int.ofNat 56) = BitVec.ofNat 64 56 := rfl
  refine ⟨_, by
    simp only [passStart, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.ea, memOp, h48, h56, State.load64, State.store64,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, reduceCtorEq, ite_false, ite_true,
      hread, hwrite, Option.map_some, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact congrArg (s.mem.readW (savedKeyAddr s) 64 + ·)
      (passOffset_signExtend component hc direction)
  · rfl
  · rfl
  · rfl
  · intro r hrax hrdi
    simp only [gpr_setReg, gpr_arithFlags, hrax, hrdi, ite_false]

end VG.Proof.TripleDes.X86_64
