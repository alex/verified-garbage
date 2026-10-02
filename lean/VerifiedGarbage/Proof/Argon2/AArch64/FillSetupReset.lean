import VerifiedGarbage.Proof.Argon2.AArch64.FillSetupDimensions
import VerifiedGarbage.Proof.Framework.Mem

/-! Reset public loop coordinates and only the pass word in the enclosing frame. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Reset (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .x19) 0) (0 : Addr)
  lane : t.gpr .x24 = 0
  slice : t.gpr .x22 = 0
  regs : ∀ r, r ∉ [Reg.x8, .x24, .x22] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem reset_ok (s : State) (write : InRegions s.wr (off (s.gpr .x19) 0) 8) :
    WP isa (.block Impl.Argon2.AArch64.FillSetup.reset) s (Reset s) := by
  apply WP.of_runBlock
  simp only [off, BitVec.add_zero] at write
  simp only [Impl.Argon2.AArch64.FillSetup.reset,
    Impl.Argon2.AArch64.Instructions.imm, Impl.Argon2.AArch64.Instructions.store,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, Size.bits, State.store, State.read,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, show (0#16).setWidth 64 = 0#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.add_zero, BitVec.setWidth_eq, write, reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.mem_write, off, BitVec.add_zero, Mem.writeW]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rfl
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
    rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

theorem Reset.pass {s t : State} (h : Reset s t) : t.mem.readW (off (t.gpr .x19) 0) 64 = 0 := by
  rw [h.mem, h.regs .x19 (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

theorem Reset.frame {s t : State} (h : Reset s t) : Frame [⟨s.gpr .x19, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (r := ⟨s.gpr .x19, 8⟩) (by simp) _
    (by simpa only [off, BitVec.add_zero] using Region.contains_self (s.gpr .x19) 8)

theorem Reset.read {s t : State} (h : Reset s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.mem, h.regs .x19 (by decide)]
  exact Mem.readW_writeW_sep (w := 64) (w' := 64)
    (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8) (Or.inr (by omega)) (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.FillSetup
