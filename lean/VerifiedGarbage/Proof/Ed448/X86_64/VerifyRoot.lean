import VerifiedGarbage.Proof.X448.X86_64.Inv
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation

/-!
# Ed448 verification's equation on x86-64: the square root's power

`root fld 12` writes only the temporaries of X448's inversion (slots 14–21)
and the product's words, and the counter `rbx` (an `ISpec`, as X448's
inversion); slot 21 ends as `rootPow` of slot 12.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Env ISpec IKeep FieldOk Scr E Outside clob opMul opSqn sqnI mulI)

/-- The slots after `root`. -/
def rootEnv (e : Env) : Env :=
  opMul 21 21 20 (opSqn 21 21 223 (opMul 21 21 12 (opSqn 21 20 1
    (opMul 20 20 14 (opSqn 20 20 2 (opMul 20 20 15 (opSqn 20 20 4 (opMul 20 20 16 (opSqn 20 20 8
    (opMul 20 20 17 (opSqn 20 20 16 (opMul 20 20 19 (opSqn 20 20 64 (opMul 20 20 19 (opSqn 20 19 64
    (opMul 19 19 18 (opSqn 19 18 32 (opMul 18 18 17 (opSqn 18 17 16 (opMul 17 17 16 (opSqn 17 16 8
    (opMul 16 16 15 (opSqn 16 15 4 (opMul 15 15 14 (opSqn 15 14 2 (opMul 14 14 12
    (opSqn 14 12 1 e)))))))))))))))))))))))))))

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem root_spec (base : Addr) : ISpec base (root fld 12) rootEnv := by
  have h : ISpec base _ _ :=
    (sqnI hf base 14 12 (by decide) 1 (by decide) (by decide)).seq <|
    (mulI hf base 14 14 12 (by decide)).seq <|
    (sqnI hf base 15 14 (by decide) 2 (by decide) (by decide)).seq <|
    (mulI hf base 15 15 14 (by decide)).seq <|
    (sqnI hf base 16 15 (by decide) 4 (by decide) (by decide)).seq <|
    (mulI hf base 16 16 15 (by decide)).seq <|
    (sqnI hf base 17 16 (by decide) 8 (by decide) (by decide)).seq <|
    (mulI hf base 17 17 16 (by decide)).seq <|
    (sqnI hf base 18 17 (by decide) 16 (by decide) (by decide)).seq <|
    (mulI hf base 18 18 17 (by decide)).seq <|
    (sqnI hf base 19 18 (by decide) 32 (by decide) (by decide)).seq <|
    (mulI hf base 19 19 18 (by decide)).seq <|
    (sqnI hf base 20 19 (by decide) 64 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 19 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 64 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 19 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 16 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 17 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 8 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 16 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 4 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 15 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 2 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 14 (by decide)).seq <|
    (sqnI hf base 21 20 (by decide) 1 (by decide) (by decide)).seq <|
    (mulI hf base 21 21 12 (by decide)).seq <|
    (sqnI hf base 21 21 (by decide) 223 (by decide) (by decide)).seq
    (mulI hf base 21 21 20 (by decide))
  exact h

theorem rootEnv_eval (e : Env) : rootEnv e 21 = rootPow (e 12) := by
  simp (config := {decide := true}) only [rootEnv, opMul, opSqn, Function.update_apply]
  rfl

theorem rootEnv_keep (e : Env) (i : Proof.X448.X86_64.Index) (hi : i.val < 14) : rootEnv e i = e i := by
  have h1 : i ≠ 14 := fun h => absurd hi (by rw [h]; decide)
  have h2 : i ≠ 15 := fun h => absurd hi (by rw [h]; decide)
  have h3 : i ≠ 16 := fun h => absurd hi (by rw [h]; decide)
  have h4 : i ≠ 17 := fun h => absurd hi (by rw [h]; decide)
  have h5 : i ≠ 18 := fun h => absurd hi (by rw [h]; decide)
  have h6 : i ≠ 19 := fun h => absurd hi (by rw [h]; decide)
  have h7 : i ≠ 20 := fun h => absurd hi (by rw [h]; decide)
  have h8 : i ≠ 21 := fun h => absurd hi (by rw [h]; decide)
  simp only [rootEnv, opMul, opSqn, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
    Function.update_of_ne h6, Function.update_of_ne h7, Function.update_of_ne h8]

end VG.Proof.Ed448.X86_64
