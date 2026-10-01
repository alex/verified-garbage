import VerifiedGarbage.Proof.Argon2.X86_64.FillSetupDimensions
import VerifiedGarbage.Proof.Framework.Mem

/-! Reset public loop coordinates and only the pass word in the enclosing frame. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Reset (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (0 : Addr)
  lane : t.gpr .rbx = 0
  slice : t.gpr .r14 = 0
  regs : ∀ r, r ∉ [Reg.rax, .rbx, .r14] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem reset_ok (s : State) (write : InRegions s.wr (off (s.gpr .rbp) 0) 8) :
    WP isa (.block Impl.Argon2.X86_64.FillSetup.reset) s (Reset s) := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.FillSetup.reset, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    write, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

theorem Reset.pass {s t : State} (h : Reset s t) : t.mem.readW (off (t.gpr .rbp) 0) 64 = 0 := by
  rw [h.mem, h.regs .rbp (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

theorem Reset.frame {s t : State} (h : Reset s t) : Frame [⟨s.gpr .rbp, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (r := ⟨s.gpr .rbp, 8⟩) (by simp) _
    (by simpa only [off, BitVec.add_zero] using Region.contains_self (s.gpr .rbp) 8)

theorem Reset.read {s t : State} (h : Reset s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.mem, h.regs .rbp (by decide)]
  exact Mem.readW_writeW_sep (w := 64) (w' := 64)
    (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8) (Or.inr (by omega)) (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.FillSetup
