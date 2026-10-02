import VerifiedGarbage.Proof.Ed25519.AArch64.PowerEnv
import VerifiedGarbage.Proof.Ed25519.RootPower

/-! The shared addition chain computes inversion and square-root powers. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def power250Env (e : Env) : Env :=
  opMul 15 16 15 (opSqn 16 16 50 (opMul 16 17 16 (opSqn 17 16 100
    (opMul 16 16 15 (opSqn 16 15 50 (opMul 15 16 15 (opSqn 16 16 10 (opMul 16 17 16 (opSqn 17 16 20
    (opMul 16 16 15 (opSqn 16 15 10 (opMul 15 16 15 (opSqn 16 15 5 (opMul 15 15 16
    (opMul 16 14 14 (opMul 14 14 15 (opMul 15 2 15 (opMul 15 15 15 (opMul 15 14 14
    (opMul 14 2 2 e))))))))))))))))))))

theorem power250_spec (base : Addr) : ISpec base power250 power250Env := by
  have h : ISpec base _ _ :=
    (sqrI base 14 2 ⟨by decide, by decide⟩).seq <|
    ((sqrI base 15 14 ⟨by decide, by decide⟩).append
      (sqrI base 15 15 ⟨by decide, by decide⟩)).seq <|
    ((((mulI base 15 2 15 ⟨by decide, by decide⟩).append
      (mulI base 14 14 15 ⟨by decide, by decide⟩)).append
      (sqrI base 16 14 ⟨by decide, by decide⟩)).append
      (mulI base 15 15 16 ⟨by decide, by decide⟩)).seq <|
    (sqnI base 16 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 15 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 17 16 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 16 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 15 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 17 16 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 16 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 15 16 15 ⟨by decide, by decide⟩)
  exact h

def invEnv (e : Env) : Env := opMul 15 15 14 (opSqn 15 15 5 (power250Env e))
def rootEnv (e : Env) : Env := opMul 15 15 2 (opSqn 15 15 2 (power250Env e))

theorem invert_spec (base : Addr) : ISpec base invert invEnv := by
  have h : ISpec base _ _ := (power250_spec base).seq ((sqnI base 15 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq
    (mulI base 15 15 14 ⟨by decide, by decide⟩))
  exact h

theorem rootPower_spec (base : Addr) : ISpec base Impl.Ed25519.AArch64.rootPower rootEnv := by
  have h : ISpec base _ _ := (power250_spec base).seq ((sqnI base 15 15 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (mulI base 15 15 2 ⟨by decide, by decide⟩))
  exact h

theorem invEnv_eval (e : Env) : invEnv e 15 = VG.Proof.X25519.invert (e 2) := by
  simp (config := {decide := true}) only [invEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem rootEnv_eval (e : Env) : rootEnv e 15 = VG.Proof.Ed25519.rootPower (e 2) := by
  simp (config := {decide := true}) only [rootEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa invert s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) :=
  WP.mono (invert_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, invEnv_eval]⟩

theorem rootPower_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa Impl.Ed25519.AArch64.rootPower s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.Ed25519.rootPower (env s.mem base 2) :=
  WP.mono (rootPower_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, rootEnv_eval]⟩

end VG.Proof.Ed25519.AArch64
