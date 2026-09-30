import VerifiedGarbage.Impl.Ed25519.X86_64.RootPower
import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine

/-! Untrusted: decoding reuses the proved field multiplication and squaring loops. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519.X86_64

def rootEnv (e : VG.Proof.X25519.X86_64.Env) : VG.Proof.X25519.X86_64.Env :=
  opMul 17 17 4 (opSqn 17 17 2 (opMul 17 18 17 (opSqn 18 18 50 (opMul 18 19 18 (opSqn 19 18 100
    (opMul 18 18 17 (opSqn 18 17 50 (opMul 17 18 17 (opSqn 18 18 10 (opMul 18 19 18 (opSqn 19 18 20
    (opMul 18 18 17 (opSqn 18 17 10 (opMul 17 18 17 (opSqn 18 17 5 (opMul 17 17 18
    (opMul 18 16 16 (opMul 16 16 17 (opMul 17 4 17 (opMul 17 17 17 (opMul 17 16 16
    (opMul 16 4 4 e))))))))))))))))))))))

theorem rootPower_spec (base : Addr) : ISpec base Impl.Ed25519.X86_64.rootPower rootEnv := by
  have h : ISpec base _ _ :=
    (mulI base 16 4 4 ⟨by decide, by decide⟩).seq <|
    ((mulI base 17 16 16 ⟨by decide, by decide⟩).append
      (mulI base 17 17 17 ⟨by decide, by decide⟩)).seq <|
    ((((mulI base 17 4 17 ⟨by decide, by decide⟩).append
      (mulI base 16 16 17 ⟨by decide, by decide⟩)).append
      (mulI base 18 16 16 ⟨by decide, by decide⟩)).append
      (mulI base 17 17 18 ⟨by decide, by decide⟩)).seq <|
    (sqnI base 18 17 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (mulI base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 18 17 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 19 18 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (mulI base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (sqnI base 18 18 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 18 17 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 19 18 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (mulI base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (sqnI base 18 18 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 17 17 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (mulI base 17 17 4 ⟨by decide, by decide⟩)
  exact h

theorem rootEnv_eval (e : VG.Proof.X25519.X86_64.Env) : rootEnv e 17 = VG.Proof.Ed25519.rootPower (e 4) := by
  simp (config := {decide := true}) only [rootEnv, opMul, opSqn, Function.update_apply]
  rfl

end VG.Proof.Ed25519.X86_64
