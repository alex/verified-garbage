import VerifiedGarbage.Impl.Argon2.AArch64.FillIterations
import VerifiedGarbage.Proof.Argon2.AArch64.FillIteration

/-! Increment, save and compare the public pass counter. -/
namespace VG.Proof.Argon2.AArch64.FillIterations
open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillIterations

theorem increment_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block increment) s fun t =>
      t.gpr .x8 = s.mem.readW (off (s.gpr .x19) 0) 64 + 1 ∧
      Divide.Keeps [.x8, .x12, .x15] s t := by
  simp only [increment, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.load_ok s .x8 .x19 0 (by decide) (by decide) hr).mono ?_
  rintro a ⟨value, ka⟩
  refine (Instructions.addi_ok a .x8 1 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, (ka.mono (by decide)).trans kt⟩
  rw [out, value]; rfl

theorem saveCheck_ok (s : State) (hw : InRegions s.wr (off (s.gpr .x19) 0) 8)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 72) 8)
    (ha : (s.gpr .x8).toNat < 2 ^ 63)
    (hb : (s.mem.readW (off (s.gpr .x19) 72) 64).toNat < 2 ^ 63) :
    WP isa (.block saveCheck) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 0) (s.gpr .x8) ∧
      (∀ r, r ∉ [Reg.x13, .x14, .x15] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x8).toNat <
        (s.mem.readW (off (s.gpr .x19) 72) 64).toNat)) := by
  simp only [saveCheck, List.flatten_cons, List.flatten_nil, List.append_nil]
  apply WP.block_append
  refine (Instructions.store_ok s .x19 .x8 0 (by decide) (by decide) hw).mono ?_
  rintro a ⟨mem, regs, rd, wr, sp⟩
  have unchanged : a.mem.readW (off (a.gpr .x19) 72) 64 =
      s.mem.readW (off (s.gpr .x19) 72) 64 := by
    rw [regs, mem]
    exact Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 72) 8 := by rw [regs, rd, wr]; exact hr
  have left : (a.gpr .x8).toNat < 2 ^ 63 := by rw [regs]; exact ha
  have right : (a.mem.readW (off (a.gpr .x19) 72) 64).toNat < 2 ^ 63 := by rw [unchanged]; exact hb
  refine (Instructions.comparem_ok a .x8 .x19 72 (by decide) (by decide) (by decide)
    read left right).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨keeps.mem.trans mem, ?_, keeps.rd.trans rd, keeps.wr.trans wr, keeps.sp.trans sp, ?_⟩
  · intro r hr; exact (keeps.regs r hr).trans (congrFun regs r)
  · change eval (.nonzero .x .x14) t = some (decide ((s.gpr .x8).toNat <
      (s.mem.readW (off (s.gpr .x19) 72) 64).toNat))
    change eval (.nonzero .x .x14) t = some (decide ((a.gpr .x8).toNat <
      (a.mem.readW (off (a.gpr .x19) 72) 64).toNat)) at flag
    rw [flag, regs, mem]
    rw [Mem.readW_writeW_sep (w := 64) (w' := 64)
      (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]

end VG.Proof.Argon2.AArch64.FillIterations
