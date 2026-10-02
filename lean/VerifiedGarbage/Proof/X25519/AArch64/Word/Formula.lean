import VerifiedGarbage.Proof.X25519.AArch64.Word.Slots

/-! The shared field operations implement precisely the RFC 7748 ladder formulas. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open Fin.CommRing

def Good (e : Env) (x1 : Fe) (st : Ladder) : Prop :=
  e 0 = x1 ∧ e 1 = st.x2 ∧ e 2 = st.z2 ∧ e 3 = st.x3 ∧ e 4 = st.z3 ∧ e 18 = a24

theorem formula_ok (e : Env) (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat)
    (hg : Good e x1 st) :
    Good (evalOps VG.Impl.X25519.AArch64.Word.stepOps
      (swapped (swapped e 1 3 ((st.swap ^^^ bit k t) == 1)) 2 4
        ((st.swap ^^^ bit k t) == 1))) x1 (ladderStep k x1 st t) := by
  obtain ⟨h0, h1, h2, h3, h4, hc⟩ := hg
  obtain ⟨e2, ez2, e3, ez3, e0, ec⟩ := stepOps_eval
    (swapped (swapped e 1 3 ((st.swap ^^^ bit k t) == 1)) 2 4 ((st.swap ^^^ bit k t) == 1))
  unfold Good
  rw [e0, e2, ez2, e3, ez3, ec, ladderStep_eq]
  by_cases hswap : st.swap ^^^ bit k t = 1 <;>
    simp (config := {decide := true}) [core, swapped,
      Spec.X25519.cswap, hswap, h0, h1, h2, h3, h4, hc, mul_comm]

end VG.Proof.X25519.AArch64.Word
