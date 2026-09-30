import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyBody
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory

/-! Untrusted: save the ABI registers and retain the three public input pointers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps Outside ea_at word_writeW_sep word_writeW_self)

theorem verifyPrepare_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdx), .mov .rdx (.reg .rcx)]) s fun t =>
      t.gpr .rax = s.gpr .rdx ∧ t.gpr .rdx = s.gpr .rcx ∧ Keeps [.rax, .rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem verifyHeaders_ok {s : State} {base : Addr} (hb : s.gpr .rdx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t =>
      t.gpr .rdi = base ∧ (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Outside base 7936 24 s.mem t.mem ∧
      t.mem.readW (off base 7936) 64 = s.gpr .rdi ∧
      t.mem.readW (off base 7944) 64 = s.gpr .rsi ∧
      t.mem.readW (off base 7952) 64 = s.gpr .rax := by
  have hw' (d : Nat) (hd : d + 8 ≤ 8192) : InRegions s.wr (off base d) 8 :=
    ⟨_, hw, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [verifyHeaders, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea_at, hb, hw' 7936 (by decide), hw' 7944 (by decide), hw' 7952 (by decide),
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact RegUpd.gpr_setReg_self _ _ _
  · exact RegUpd.gpr_setReg_of_ne _ _ hr
  · exact (((Outside.refl base 7936 24 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _
  all_goals simp (disch := decide) only [RegUpd.mem_setReg, word_writeW_sep, word_writeW_self]

theorem verifyFinishArgs_ok (s : State) :
    WP isa (.block [.mov .rdx (.reg .rdi)]) s fun t =>
      t.gpr .rdx = s.gpr .rdi ∧ Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg_self,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

end VG.Proof.Ed25519.X86_64
