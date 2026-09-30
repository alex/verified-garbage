import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyBody
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory

/-! Untrusted: save the ABI registers and retain the three public input pointers. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyPrepare_ok (s : State) :
    WP isa (.block [mov .x8 .x2, mov .x2 .x3]) s fun t =>
      t.gpr .x8 = s.gpr .x2 ∧ t.gpr .x2 = s.gpr .x3 ∧ Keeps [.x8, .x2] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem verifyHeaders_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t =>
      t.gpr .x0 = base ∧ (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Outside base 7936 24 s.mem t.mem ∧
      t.mem.readW (off base 7936) 64 = s.gpr .x0 ∧
      t.mem.readW (off base 7944) 64 = s.gpr .x1 ∧
      t.mem.readW (off base 7952) 64 = s.gpr .x8 := by
  have hw' (d : Nat) (hd : d + 8 ≤ 8192) : InRegions s.wr (off base d) 8 :=
    ⟨_, hw, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [verifyHeaders, mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.store, addr, Size.bytes, hb, hw' 7936 (by decide), hw' 7944 (by decide), hw' 7952 (by decide),
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, BitVec.setWidth_eq,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.mem_write]
    exact (((Outside.refl base 7936 24 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _
  all_goals simp (disch := decide) only [RegUpd.mem_write, write64_eq_writeW, word_writeW_sep, word_writeW_self]

theorem verifyFinishArgs_ok (s : State) :
    WP isa (.block [mov .x2 .x0, mov .x0 .x8]) s fun t =>
      t.gpr .x2 = s.gpr .x0 ∧ t.gpr .x0 = s.gpr .x8 ∧ Keeps [.x2, .x0] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Ed25519.AArch64
