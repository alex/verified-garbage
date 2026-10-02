import VerifiedGarbage.Proof.Ed25519.Arm.PowerEnv
import VerifiedGarbage.Proof.Ed25519.RootPower

/-! The shared addition chain computes inversion and square-root powers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def power250Env (e : Env) : Env :=
  opMul 15 16 15 (opSqn 16 16 50 (opMul 16 17 16 (opSqn 17 16 100
    (opMul 16 16 15 (opSqn 16 15 50 (opMul 15 16 15 (opSqn 16 16 10 (opMul 16 17 16 (opSqn 17 16 20
    (opMul 16 16 15 (opSqn 16 15 10 (opMul 15 16 15 (opSqn 16 15 5 (opMul 15 15 16
    (opMul 16 14 14 (opMul 14 14 15 (opMul 15 2 15 (opMul 15 15 15 (opMul 15 14 14
    (opMul 14 2 2 e))))))))))))))))))))

theorem power250_spec (base : BitVec 32) : ISpec base power250 power250Env := by
  exact
    (mulI base 14 2 2).seq <|
    (mulI base 15 14 14).seq <|
    (mulI base 15 15 15).seq <|
    (mulI base 15 2 15).seq <|
    (mulI base 14 14 15).seq <|
    (mulI base 16 14 14).seq <|
    (mulI base 15 15 16).seq <|
    (sqnI base 16 15 5 (by decide) (by decide)).seq <|
    (mulI base 15 16 15).seq <|
    (sqnI base 16 15 10 (by decide) (by decide)).seq <|
    (mulI base 16 16 15).seq <|
    (sqnI base 17 16 20 (by decide) (by decide)).seq <|
    (mulI base 16 17 16).seq <|
    (sqnI base 16 16 10 (by decide) (by decide)).seq <|
    (mulI base 15 16 15).seq <|
    (sqnI base 16 15 50 (by decide) (by decide)).seq <|
    (mulI base 16 16 15).seq <|
    (sqnI base 17 16 100 (by decide) (by decide)).seq <|
    (mulI base 16 17 16).seq <|
    (sqnI base 16 16 50 (by decide) (by decide)).seq <|
    (mulI base 15 16 15)

def invEnv (e : Env) : Env := opMul 15 15 14 (opSqn 15 15 5 (power250Env e))
def rootEnv (e : Env) : Env := opMul 15 15 2 (opSqn 15 15 2 (power250Env e))

theorem invert_spec (base : BitVec 32) : ISpec base invert invEnv := by
  have h : ISpec base _ _ := (power250_spec base).seq ((sqnI base 15 15 5 (by decide) (by decide)).seq
    (mulI base 15 15 14))
  exact h

theorem rootPower_spec (base : BitVec 32) : ISpec base Impl.Ed25519.Arm.rootPower rootEnv := by
  have h : ISpec base _ _ := (power250_spec base).seq ((sqnI base 15 15 2 (by decide) (by decide)).seq
    (mulI base 15 15 2))
  exact h

theorem invEnv_eval (e : Env) : invEnv e 15 = VG.Proof.X25519.invert (e 2) := by
  simp (config := {decide := true}) only [invEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem rootEnv_eval (e : Env) : rootEnv e 15 = VG.Proof.Ed25519.rootPower (e 2) := by
  simp (config := {decide := true}) only [rootEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem invert_ok {s : State} {base : BitVec 32} (hs : Ctx base s) (hl : AllLim s.mem base) :
    WP isa invert s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) :=
  WP.mono (invert_spec base s hs hl) fun _ ⟨hk, hlt, hv⟩ => ⟨hk, hlt, by rw [hv, invEnv_eval]⟩

theorem rootPower_ok {s : State} {base : BitVec 32} (hs : Ctx base s) (hl : AllLim s.mem base) :
    WP isa Impl.Ed25519.Arm.rootPower s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 15 = VG.Proof.Ed25519.rootPower (env s.mem base 2) :=
  WP.mono (rootPower_spec base s hs hl) fun _ ⟨hk, hlt, hv⟩ => ⟨hk, hlt, by rw [hv, rootEnv_eval]⟩

end VG.Proof.Ed25519.Arm
