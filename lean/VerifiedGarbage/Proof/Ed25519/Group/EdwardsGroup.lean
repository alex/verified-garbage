import VerifiedGarbage.Proof.Ed25519.Group.Edwards
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic

/-!
# The points of a complete twisted Edwards curve form a commutative group

Untrusted. `EPoint d` is the type of affine points; its addition is the
Edwards law of `Edwards.lean`, its zero `(0, 1)` and its negation
`(-x, y)`.
-/

namespace VG.Proof.Ed25519.Edwards

variable {F : Type*} [Field F]

/-- An affine point of the curve. -/
@[ext]
structure EPoint (d : F) where
  x : F
  y : F
  on : OnCurve d x y

variable {d : F}

instance : Zero (EPoint d) := ⟨⟨0, 1, by unfold OnCurve; ring⟩⟩

instance : Neg (EPoint d) := ⟨fun p => ⟨-p.x, p.y, by have := p.on; unfold OnCurve at *; linear_combination this⟩⟩

@[simp] theorem zero_x : (0 : EPoint d).x = 0 := rfl
@[simp] theorem zero_y : (0 : EPoint d).y = 1 := rfl
@[simp] theorem neg_x (p : EPoint d) : (-p).x = -p.x := rfl
@[simp] theorem neg_y (p : EPoint d) : (-p).y = p.y := rfl

variable [hP : Fact (Params d)]

instance : Add (EPoint d) :=
  ⟨fun p q => ⟨addX d p.x p.y q.x q.y, addY d p.x p.y q.x q.y, onCurve_add hP.out p.on q.on⟩⟩

@[simp] theorem add_x (p q : EPoint d) : (p + q).x = addX d p.x p.y q.x q.y := rfl
@[simp] theorem add_y (p q : EPoint d) : (p + q).y = addY d p.x p.y q.x q.y := rfl
theorem add_assoc' (p q r : EPoint d) : p + q + r = p + (q + r) :=
  EPoint.ext (add_assoc_x hP.out p.on q.on r.on) (add_assoc_y hP.out p.on q.on r.on)

theorem zero_add' (p : EPoint d) : 0 + p = p := by
  ext <;> simp [addX, addY]

theorem add_comm' (p q : EPoint d) : p + q = q + p := by
  ext <;> simp only [add_x, add_y, addX, addY] <;> ring_nf

theorem neg_add_cancel' (p : EPoint d) : -p + p = 0 := by
  have h := den_sub_ne hP.out (-p).on p.on
  have hc := p.on
  unfold OnCurve at hc
  ext
  · simp [addX]; ring_nf; simp
  · simp only [add_y, neg_x, neg_y, zero_y, addY] at h ⊢
    rw [div_eq_one_iff_eq h]
    linear_combination hc

instance : AddCommGroup (EPoint d) where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero p := by rw [add_comm', zero_add']
  add_comm := add_comm'
  neg_add_cancel := neg_add_cancel'
  nsmul := nsmulRec
  zsmul := zsmulRec

end VG.Proof.Ed25519.Edwards
