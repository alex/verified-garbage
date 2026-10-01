import VerifiedGarbage.Proof.X448.AArch64.Square

/-!
# X448 on AArch64: inversion

Untrusted: everything here is checked by Lean. The addition chain updates
slots 14–21 and leaves the ladder's coordinates available for the final
multiplication and encoding.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- The field slots after the inversion's addition chain. -/
def invEnv (e : Env) : Env :=
  let e := applyOps [.copy 14 2] e
  let e := opSqn 14 1 e
  let e := applyOps [.mul 14 14 2, .copy 15 14] e
  let e := opSqn 15 2 e
  let e := applyOps [.mul 15 15 14, .copy 16 15] e
  let e := opSqn 16 4 e
  let e := applyOps [.mul 16 16 15, .copy 17 16] e
  let e := opSqn 17 8 e
  let e := applyOps [.mul 17 17 16, .copy 18 17] e
  let e := opSqn 18 16 e
  let e := applyOps [.mul 18 18 17, .copy 19 18] e
  let e := opSqn 19 32 e
  let e := applyOps [.mul 19 19 18, .copy 20 19] e
  let e := opSqn 20 64 e
  let e := applyOps [.mul 20 20 19] e
  let e := opSqn 20 64 e
  let e := applyOps [.mul 20 20 19] e
  let e := opSqn 20 16 e
  let e := applyOps [.mul 20 20 17] e
  let e := opSqn 20 8 e
  let e := applyOps [.mul 20 20 16] e
  let e := opSqn 20 4 e
  let e := applyOps [.mul 20 20 15] e
  let e := opSqn 20 2 e
  let e := applyOps [.mul 20 20 14, .copy 21 20] e
  let e := opSqn 21 1 e
  let e := applyOps [.mul 21 21 2] e
  let e := opSqn 21 225 e
  let e := opSqn 20 2 e
  applyOps [.mul 20 20 2, .mul 21 21 20] e

theorem invert_spec (base : Addr) : ISpec base Impl.X448.AArch64.invert invEnv := by
  have h : ISpec base _ _ :=
    (opsI base [.copy 14 2]).seq <|
    (sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 14 14 2, .copy 15 14]).seq <|
    (sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 15 15 14, .copy 16 15]).seq <|
    (sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 16 16 15, .copy 17 16]).seq <|
    (sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 17 17 16, .copy 18 17]).seq <|
    (sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 18 18 17, .copy 19 18]).seq <|
    (sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (opsI base [.mul 19 19 18, .copy 20 19]).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19]).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19]).seq <|
    (sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 17]).seq <|
    (sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 16]).seq <|
    (sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 15]).seq <|
    (sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 14, .copy 21 20]).seq <|
    (sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 21 21 2]).seq <|
    (sqnI base 21 (n := 225) (by decide) (by decide)).seq <|
    (sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 2, .mul 21 21 20])
  exact h

theorem invEnv_eval (e : Env) : invEnv e 21 = Proof.X448.invert (e 2) := by
  simp (config := {decide := true}) only [invEnv, applyOps, FieldOp.apply, opMul, opCopy, opSqn,
    Function.update_apply]
  rfl

theorem invEnv_x2 (e : Env) : invEnv e 1 = e 1 := by
  simp (config := {decide := true}) only [invEnv, applyOps, FieldOp.apply, opMul, opCopy, opSqn,
    Function.update_apply, ite_true, ite_false]

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa Impl.X448.AArch64.invert s fun t =>
      IKeep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = invEnv (E s.mem base) :=
  invert_spec base s hs hb

end VG.Proof.X448.AArch64
