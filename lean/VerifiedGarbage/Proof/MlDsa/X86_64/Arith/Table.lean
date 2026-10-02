import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic

/-!
# ML-DSA on x86-64: tables of constants in the working space

A table of `u32`s in the working space (`Tab`), which writes elsewhere keep
(`Tab.frame`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (coeffAt)

/-- The first `n` entries of the table `t` are the `u32`s at `p`. -/
def Tab (t : Nat → Nat) (m : Mem) (p : Addr) (n : Nat) : Prop :=
  ∀ k < n, coeffAt m p k = BitVec.ofNat 32 (t k)

/-- Writes elsewhere keep the table. -/
theorem Tab.frame {t : Nat → Nat} {m m' : Mem} {p : Addr} {n : Nat} (h : Tab t m p n) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (pR p).Disjoint r) (hn : n ≤ 256) : Tab t m' p n :=
  fun k hk => by rw [coeffAt_frame hf hd (show k < 256 by omega)]; exact h k hk

end VG.Proof.MlDsa.X86_64.Arith
