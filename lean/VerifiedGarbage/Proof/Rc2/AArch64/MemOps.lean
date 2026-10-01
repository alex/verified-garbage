import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd

theorem readByte (m : Mem) (p : Addr) : m.read p 1 = m p := by
  change (0#0 ++ m p) = _
  exact BitVec.zero_width_append _ _

theorem exec_ldr_x (s : State) (t n : Reg) (off : Nat)
    (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.ldr .x t n off) s =
      some (s.write .x t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)) := by
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, Option.bind_some,
    State.load, h, Option.map_some, Mem.readW]

theorem exec_str_x (s : State) (t n : Reg) (off : Nat)
    (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.str .x t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) } := by
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, Option.bind_some,
    State.store, h, State.read, BitVec.setWidth_eq, Mem.writeW]

end VG.Proof.Rc2.AArch64
