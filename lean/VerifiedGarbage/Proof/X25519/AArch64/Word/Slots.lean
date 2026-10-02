import VerifiedGarbage.Impl.X25519.AArch64.Word
import VerifiedGarbage.Proof.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.Ed25519.AArch64.Swap
import VerifiedGarbage.Proof.Ed25519.AArch64.Freeze
import VerifiedGarbage.Proof.X25519.Ladder

/-! The four-word field backend in X25519's existing 4 KiB workspace. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

abbrev Scratch (s : State) (base : Addr) := Scr s base false

def swapped (e : Env) (x y : Slot) (sw : Bool) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem swapField_ok {s : State} {base : Addr} (hs : Scratch s base)
    (x y : Slot) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block (VG.Impl.Ed25519.AArch64.cswap (offset x) (offset y))) s fun t =>
      Keep base s t ∧ env t.mem base = swapped (env s.mem base) x y sw ∧ t.gpr .x3 = s.gpr .x3 := by
  have hsep : offset x + 32 ≤ offset y ∨ offset y + 32 ≤ offset x := by
    have : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    simp only [offset]; omega
  refine WP.mono (VG.Proof.Ed25519.AArch64.cswap_ok hs
    (slot_rangeWith (large := false) x) (slot_rangeWith (large := false) y) hsep hm)
    fun t ⟨hg, hm3, hr, hw, hp, ⟨m, h₁, h₂, hx⟩, _, hy⟩ => ?_
  refine ⟨⟨hg, hr, hw, hp, (h₁.mono (by simp [offset]) (by simp only [offset]; omega)).trans
    (h₂.mono (by simp [offset]) (by simp only [offset]; omega))⟩, ?_, hm3⟩
  have ex : F m base (offset x) = if sw then env s.mem base y else env s.mem base x := by
    change Proof.X25519.toFe _ = _
    rw [hx]
    cases sw <;> rfl
  have ey : F t.mem base (offset y) = if sw then env s.mem base x else env s.mem base y := by
    change Proof.X25519.toFe _ = _
    rw [hy]
    cases sw <;> rfl
  rw [env_update y h₂, env_update x h₁, ex, ey]
  rfl

/-- The coordinate formulas after the conditional swaps. -/
def core (e : Env) : Spec.X25519.Ladder :=
  let a := e 1 + e 2
  let aa := a * a
  let b := e 1 - e 2
  let bb := b * b
  let ee := aa - bb
  let da := (e 3 - e 4) * a
  let cb := (e 3 + e 4) * b
  ⟨aa * bb, ee * (aa + ee * e 18),
    (da + cb) * (da + cb), e 0 * ((da - cb) * (da - cb)), 0⟩

theorem stepOps_eval (e : Env) :
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 1 = (core e).x2 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 2 = (core e).z2 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 3 = (core e).x3 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 4 = (core e).z3 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 0 = e 0 ∧
    (evalOps VG.Impl.X25519.AArch64.Word.stepOps e) 18 = e 18 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end VG.Proof.X25519.AArch64.Word
