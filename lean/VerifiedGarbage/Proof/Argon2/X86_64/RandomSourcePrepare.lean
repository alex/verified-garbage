import VerifiedGarbage.Impl.Argon2.X86_64.RandomSource
import VerifiedGarbage.Proof.Argon2.X86_64.AddressMode
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheInvariant
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheMatrix

/-! Retain the source invariants while selecting the public addressing mode. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.RandomSource

structure Ready (p : Params) (pass lane slice index old : Nat) (s : State) : Prop where
  filling : FillKernel.Ready p pass lane slice index s
  cache : AddressCache.Invariant p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩

theorem Ready.of_keeps {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Ready p pass lane slice index old t := by
  refine ⟨h.filling.of_keeps k, h.cache.of_keeps k, ?_⟩
  have matrix : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [k.mem, k.regs .rbp (by decide)]
  have work : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work; rw [k.mem, k.regs .rbp (by decide)]
  rw [matrix, work]; exact h.matrixWork

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    t.zf = decide (s.gpr .r10 = 0#64) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [test, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change (s.gpr .r10 - 0#64 == 0#64) = decide (s.gpr .r10 = 0#64)
    rw [BitVec.sub_zero]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

theorem bool_zero : ∀ b : Bool, decide ((BitVec.ofBool b).setWidth 64 = 0#64) = !b := by
  decide +kernel

theorem prepare_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) : WP isa prepare s fun t =>
      t.zf = !independent p pass slice ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold prepare
  refine WP.seq ((AddressMode.code_spec_ok s p pass slice
    (h.cache.reads 112 (by simp)) (h.cache.reads 0 (by simp))
    h.cache.words.variantWord h.filling.passWord h.filling.position.slice
    (Nat.lt_trans h.filling.bounds.passBound (by decide))
    (Nat.lt_trans h.filling.bounds.sliceBound (by decide))).mono ?_)
  rintro a ⟨mode, keeps⟩
  refine (test_ok a).mono ?_
  rintro t ⟨flag, tested⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tested.mono (by decide))⟩
  rw [flag, mode, bool_zero]

end VG.Proof.Argon2.X86_64.RandomSource
