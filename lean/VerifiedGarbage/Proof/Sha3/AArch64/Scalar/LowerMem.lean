import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lower
import VerifiedGarbage.Proof.Framework.AArch64.Inline

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

private theorem exec_dup (s : VG.AArch64.State) (v : VReg) (r : Reg) :
    exec (.vop (.dup .d2 v r)) s =
      some (s.setV v (ofVDwords (s.gpr r) (s.gpr r))) := rfl
private theorem exec_umov (s : VG.AArch64.State) (r : Reg) (v : VReg) :
    exec (.umov .x r v 0) s = some (s.write .x r (vdword (s.v v) 0)) := rfl
private theorem write_gpr (s : VG.AArch64.State) (d r : Reg) (v : BitVec 64) :
    (s.write .x d v).gpr r = if r = d then v else s.gpr r := by
  simp only [RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq]

/-- v31 names the spill pair; x30 is preserved even if it currently contains
an algorithm temporary rather than the spill address. -/
theorem spill_lower_ok (s : VG.AArch64.State) (p : Addr) (k : Nat) (a : Reg)
    (hk : k < 2) (ha : a ≠ .x30) (hp : vdword (s.v .v31) 0 = p)
    (hi : InRegions s.wr (p + BitVec.ofNat 64 (lowerSpillOffset k)) 8) :
    ∃ s', runBlock isa (lower (.spill k a)) s = some s' ∧
      (∀ r, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (p + BitVec.ofNat 64 (lowerSpillOffset k)) (s.gpr a) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v28 → s'.v v = s.v v) := by
  let t := (s.setV .v28 (ofVDwords (s.gpr .x30) (s.gpr .x30))).write .x .x30 p
  have htp : t.gpr .x30 = p := by simp only [t, write_gpr, eq_self, ite_true]
  have hta : t.gpr a = s.gpr a := by simp only [t, write_gpr, ite_eq_right ha, RegUpd.gpr_setV]
  have htmem : t.mem = s.mem := rfl
  have htwr : t.wr = s.wr := rfl
  have hst : exec (.str .x a .x30 (lowerSpillOffset k)) t =
      some { t with mem := s.mem.writeW (p + BitVec.ofNat 64 (lowerSpillOffset k)) (s.gpr a) } := by
    rw [exec_str_x (by simp only [lowerSpillOffset]; omega : lowerSpillOffset k % 8 = 0 ∧ lowerSpillOffset k < 32768)]
    · rw [htp, hta, htmem]
    · rw [htwr, htp]; exact hi
  let u := { t with mem := s.mem.writeW (p + BitVec.ofNat 64 (lowerSpillOffset k)) (s.gpr a) }
  refine ⟨u.write .x .x30 (s.gpr .x30), ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [lower, runBlock_cons, exec_dup, exec_umov, runStep_some, RegUpd.v_setV,
      show VReg.v31 ≠ .v28 by decide, ite_false, hp]
    rw [hst]
    simp only [runStep_some, runBlock_cons, exec_umov, u, t, RegUpd.v_write, RegUpd.v_setV,
      eq_self, ite_true, vdword_ofVDwords_0, runBlock_nil]
  · intro r
    simp only [u, t, write_gpr, RegUpd.gpr_setV]
    by_cases h : r = .x30
    · subst r; simp only [eq_self, ite_true]
    · simp only [ite_eq_right h]
  · intro v hv
    simp only [u, t, RegUpd.v_write, RegUpd.v_setV, ite_eq_right hv]

theorem reload_lower_ok (s : VG.AArch64.State) (p : Addr) (k : Nat) (d : Reg)
    (hk : k < 2) (hd : d ≠ .x30) (hp : vdword (s.v .v31) 0 = p)
    (hi : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (lowerSpillOffset k)) 8) :
    ∃ s', runBlock isa (lower (.reload d k)) s = some s' ∧
      (∀ r, s'.gpr r = if r = d then s.mem.readW (p + BitVec.ofNat 64 (lowerSpillOffset k)) 64 else s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v28 → s'.v v = s.v v) := by
  let t := (s.setV .v28 (ofVDwords (s.gpr .x30) (s.gpr .x30))).write .x .x30 p
  have htp : t.gpr .x30 = p := by simp only [t, write_gpr, eq_self, ite_true]
  have htmem : t.mem = s.mem := rfl
  have htrd : t.rd = s.rd := rfl
  have htwr : t.wr = s.wr := rfl
  have hld : exec (.ldr .x d .x30 (lowerSpillOffset k)) t =
      some (t.write .x d (s.mem.readW (p + BitVec.ofNat 64 (lowerSpillOffset k)) 64)) := by
    rw [exec_ldr_x (by simp only [lowerSpillOffset]; omega : lowerSpillOffset k % 8 = 0 ∧ lowerSpillOffset k < 32768)]
    · rw [htp, htmem]
    · rw [htrd, htwr, htp]; exact hi
  let u := t.write .x d (s.mem.readW (p + BitVec.ofNat 64 (lowerSpillOffset k)) 64)
  refine ⟨u.write .x .x30 (s.gpr .x30), ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [lower, runBlock_cons, exec_dup, exec_umov, runStep_some, RegUpd.v_setV,
      show VReg.v31 ≠ .v28 by decide, ite_false, hp]
    rw [hld]
    simp only [runStep_some, runBlock_cons, exec_umov, u, t, RegUpd.v_write, RegUpd.v_setV,
      eq_self, ite_true, vdword_ofVDwords_0, runBlock_nil]
  · intro r
    simp only [u, t, write_gpr, RegUpd.gpr_setV]
    by_cases hr : r = .x30
    · subst r; simp only [eq_self, ite_true, ite_eq_right (Ne.symm hd)]
    · simp only [ite_eq_right hr]
  · intro v hv
    simp only [u, t, RegUpd.v_write, RegUpd.v_setV, ite_eq_right hv]

end VG.Proof.Sha3.AArch64.Scalar
