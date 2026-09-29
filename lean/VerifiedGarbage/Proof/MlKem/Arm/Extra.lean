import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM: lemmas the ARMv7 top-level functions use

Untrusted: everything here is checked by Lean. Target-independent facts
about the sponge's output and the algorithms of ML-KEM-768 that the proofs
of the top-level functions on 32-bit ARM need.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem
open VG.Spec.Sha3 (squeezeFrom)

/-- Output continued from matching positions of two states is the same. -/
theorem squeezeFrom_shift {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) {S P : Spec.Sha3.State}
    {p c : Nat} (h : ∀ d, squeezeFrom rate S p d = squeezeFrom rate P c d) (a d : Nat) :
    squeezeFrom rate S (p + a) d = squeezeFrom rate P (c + a) d := by
  have e : ∀ (T : Spec.Sha3.State) (x : Nat), squeezeFrom rate T (x + a) d = (squeezeFrom rate T x (a + d)).drop a :=
    fun T x => by
      rw [← squeezeFrom_append hr hr' T x a d, List.drop_left' (VG.Proof.Sha3.length_squeezeFrom hr hr' T x a)]
  rw [e S p, e P c, h]

end VG.Proof.MlKem
