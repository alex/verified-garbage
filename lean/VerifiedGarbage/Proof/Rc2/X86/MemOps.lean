import VerifiedGarbage.Proof.Rc2.X86.KeySteps

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem exec_load (s : State) (t n : Reg) (off : Nat)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions (s.rd ++ s.wr) (addr32 (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.mov t (.mem (memOp n off))) s =
      some (s.setReg t (s.mem.readW (addr32 (s.gpr n) + BitVec.ofNat 64 off) 32)) := by
  change (State.load32 s (addr32 (s.gpr n + BitVec.ofNat 32 off))).map (s.setReg t) = _
  rw [addr_add fit]
  simp only [State.load32, h, ite_true, Option.map_some]

theorem exec_store (s : State) (t n : Reg) (off : Nat)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions s.wr (addr32 (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.store (memOp n off) t) s =
      some {s with mem := s.mem.writeW (addr32 (s.gpr n) + BitVec.ofNat 64 off) (s.gpr t)} := by
  change State.store32 s (addr32 (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t) = _
  rw [addr_add fit]
  simp only [State.store32, h, ite_true]

end VG.Proof.Rc2.X86
