import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Entry
import VerifiedGarbage.Proof.Framework.RelCT

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

theorem block_cons_ct {i : Instr} {is : List Instr} {P R Q : State → State → Prop}
    (hi : ∀ a b a' b', P a b → exec i a = some a' → exec i b = some b' →
      addrs i a = addrs i b ∧ R a' b')
    (ht : RelCT isa R (.block is) Q) : RelCT isa P (.block (i :: is)) Q := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      cases ha : exec i a with
      | none => simp only [execBlock, ha, reduceCtorEq] at ea
      | some u =>
        cases hb : exec i b with
        | none => simp only [execBlock, hb, reduceCtorEq] at eb
        | some v =>
          simp only [execBlock, ha, hb, Option.map_eq_some_iff,
            Prod.exists, Prod.mk.injEq] at ea eb
          obtain ⟨u', tr, eu, rfl, rfl⟩ := ea
          obtain ⟨v', ts, ev, rfl, rfl⟩ := eb
          obtain ⟨he, hr⟩ := hi a b u v hp ha hb
          obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ hr (.block eu) (.block ev)
          exact ⟨by change (addrs i a).map Leak.addr ++ tr = _; rw [he], hq⟩

theorem block_nil_ct {P : State → State → Prop} : RelCT isa P (.block []) P := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at ea eb
      obtain ⟨rfl, rfl⟩ := ea
      obtain ⟨rfl, rfl⟩ := eb
      exact ⟨rfl, hp⟩

theorem block_append_ct {xs ys : List Instr} {P R Q : State → State → Prop}
    (hx : RelCT isa P (.block xs) R) (hy : RelCT isa R (.block ys) Q) :
    RelCT isa P (.block (xs ++ ys)) Q := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      rw [VG.execBlock_append] at ea eb
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.exists, Prod.mk.injEq] at ea eb
      obtain ⟨u, tx, ex, v, ty, ey, rfl, rfl⟩ := ea
      obtain ⟨u', tx', ex', v', ty', ey', rfl, rfl⟩ := eb
      obtain ⟨rfl, hr⟩ := hx _ _ _ _ _ _ hp (.block ex) (.block ex')
      obtain ⟨rfl, hq⟩ := hy _ _ _ _ _ _ hr (.block ey) (.block ey')
      exact ⟨rfl, hq⟩

private theorem store_ct (r : Reg) (off : Nat) :
    RelCT isa (fun a b => a.sp = b.sp)
      (.block [.addSp .r12 248, .str r .r12 off]) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
  · intro a b a' b' hp ha hb
    simp only [exec, show 248 < 256 from by decide, ite_true, Option.some.injEq] at ha hb
    subst a' b'
    exact ⟨rfl, hp, congrArg (· + BitVec.ofNat 32 248) hp⟩
  · apply block_cons_ct (ht := block_nil_ct)
    intro a b a' b' hp ha hb
    exact ⟨by simp only [addrs, hp.2], (exec_sp ha).trans (hp.1.trans (exec_sp hb).symm)⟩

theorem saveWord_ct (j : Nat) : RelCT isa (fun a b => a.sp = b.sp)
    (.block (saveWord j)) (fun a b => a.sp = b.sp) := by
  by_cases h : j < 4
  · simp only [saveWord, h, ite_true, List.nil_append]
    exact store_ct _ _
  · simp only [saveWord, h, ite_false, List.cons_append, List.nil_append]
    apply block_cons_ct (ht := store_ct _ _)
    intro a b a' b' hp ha hb
    exact ⟨by simp only [addrs, hp], (exec_sp ha).trans (hp.trans (exec_sp hb).symm)⟩

theorem saveArgs_ct (n : Nat) : RelCT isa (fun a b => a.sp = b.sp)
    (.block (saveArgs n)) (fun a b => a.sp = b.sp) := by
  induction n with
  | zero => exact block_nil_ct
  | succ n ih =>
    simp only [saveArgs, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact block_append_ct ih (saveWord_ct n)

end VG.Proof.Ed25519.Arm.Whole
