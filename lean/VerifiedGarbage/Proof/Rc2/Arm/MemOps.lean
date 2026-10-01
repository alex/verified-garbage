import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

namespace VG.Proof.Rc2.Arm

open VG VG.Arm

theorem exec_ldr (s : State) (t n : Reg) (off : Nat) (ho : off < 4096)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.ldr t n off) s =
      some (s.setReg t (s.mem.readW (State.addr (s.gpr n) + BitVec.ofNat 64 off) 32)) := by
  simp only [exec, ho, ite_true, State.load32, addr_add fit, h, Option.map_some]

theorem exec_str (s : State) (t n : Reg) (off : Nat) (ho : off < 4096)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions s.wr (State.addr (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.str t n off) s =
      some {s with mem := s.mem.writeW (State.addr (s.gpr n) + BitVec.ofNat 64 off) (s.gpr t)} := by
  simp only [exec, ho, ite_true, State.store32, addr_add fit, h]

end VG.Proof.Rc2.Arm
