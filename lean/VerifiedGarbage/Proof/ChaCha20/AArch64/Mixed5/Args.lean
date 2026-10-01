import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5

structure SavedArgs (len data : Addr) (s : State) : Prop where
  len : s.gpr .x19 = len
  data : s.gpr .x26 = data

theorem saveArgs_ok (s : State) : WP isa (.block saveArgs) s fun u =>
    SavedArgs (s.gpr .x2) (s.gpr .x1) u ∧
    (∀ r, r ≠ .x19 → r ≠ .x26 → u.gpr r = s.gpr r) ∧
    u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [saveArgs,runBlock_cons,runBlock_nil,exec,
    State.read,Size.bits,ite_true,isa,runStep_some,RegUpd.gpr_write,
    BitVec.setWidth_eq,BitVec.add_zero,Option.some.injEq,exists_eq_left']
  exact ⟨⟨rfl,rfl⟩,fun r h21 h22 => by simp only [h21,h22,ite_false],rfl,rfl,rfl,rfl,rfl⟩

theorem restoreArgs_ok (s : State) {len data : Addr} (h : SavedArgs len data s) :
    WP isa (.block restoreArgs) s fun u =>
      u.gpr .x1 = data ∧ u.gpr .x2 = len ∧ u.gpr .x3 = s.gpr .x20 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restoreArgs,runBlock_cons,runBlock_nil,exec,
    State.read,Size.bits,ite_true,isa,runStep_some,RegUpd.gpr_write,
    BitVec.setWidth_eq,BitVec.add_zero,Option.some.injEq,exists_eq_left',h.len,h.data]
  exact ⟨rfl,rfl,rfl,fun r h1 h2 h3 => by simp only [h1,h2,h3,ite_false],rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.ChaCha20.AArch64.Mixed5
