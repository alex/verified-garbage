import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
import VerifiedGarbage.Proof.X448.X86_64.Env
import VerifiedGarbage.Proof.Ed448.Group.Projective

/-!
# Ed448 base-point multiplication on x86-64: field programs

A list of field operations on the slots (`FOp`) runs as X448's verified
field arithmetic (`mulE`, `sqrE`, `addE`, `subE`), for any correct field
multiplications (`FieldOk`): the slots become the operations' evaluation
(`evalOps`), and nothing else changes but the registers `clob` and the
memory in `[64, 1648)`. The doubling and the addition programs evaluate to
the formulas of RFC 8032 §5.2.4 (`double` and the specification's
`pointAdd`), in their stated order.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk mulE sqrE addE subE opMul opAdd opSub)

/-- A slot by its number (below 22 in every program here). -/
def idx (n : Nat) : Index := ⟨n % 22, Nat.mod_lt _ (by decide)⟩

def fopValid : FOp → Prop
  | .mul o a b | .add o a b | .sub o a b => o < 22 ∧ a < 22 ∧ b < 22
  | .sqr o a => o < 22 ∧ a < 22

instance (op : FOp) : Decidable (fopValid op) := by cases op <;> unfold fopValid <;> infer_instance

def evalOp : FOp → Env → Env
  | .mul o a b => opMul (idx o) (idx a) (idx b)
  | .sqr o a => opMul (idx o) (idx a) (idx a)
  | .add o a b => opAdd (idx o) (idx a) (idx b)
  | .sub o a b => opSub (idx o) (idx a) (idx b)

def evalOps (ops : List FOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

theorem slot_idx {n : Nat} (h : n < 22) : Impl.X448.X86_64.slot n = Impl.X448.X86_64.slot (idx n).val := by
  simp only [idx, Nat.mod_eq_of_lt h]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem fop_ok {s : State} {base : Addr} (hs : Scr s base) (op : FOp) (hv : fopValid op) :
    WP isa (.block (op.code fld)) s fun t =>
      Keep base s t ∧ E t.mem base = evalOp op (E s.mem base) := by
  cases op with
  | mul o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [FOp.code, slot_idx h1, slot_idx h2, slot_idx h3]
    exact mulE hf hs _ _ _
  | sqr o a =>
    obtain ⟨h1, h2⟩ := hv
    simp only [FOp.code, slot_idx h1, slot_idx h2]
    exact sqrE hf hs _ _
  | add o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [FOp.code, slot_idx h1, slot_idx h2, slot_idx h3]
    exact addE hs _ _ _
  | sub o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [FOp.code, slot_idx h1, slot_idx h2, slot_idx h3]
    exact subE hs _ _ _

include hf in
theorem fieldCode_ok (ops : List FOp) (hv : ∀ op ∈ ops, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) :
    WP isa (.block (fieldCode fld ops)) s fun t =>
      Keep base s t ∧ E t.mem base = evalOps ops (E s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fop_ok hf hs op (hv op List.mem_cons_self)) fun t ⟨ht, et⟩ => ?_
    refine WP.mono (ih (fun o h => hv o (List.mem_cons_of_mem _ h)) (ht.scr hs))
      fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et]; rfl⟩

/-! ## The point formulas -/

/-- The point in slots `i`, `j`, `k`. -/
def pt (e : Env) (i j k : Index) : Spec.Ed448.Point := ⟨e i, e j, e k⟩

/-- The specification's addition, with `d` a parameter. -/
def addWith (dd : Spec.X448.Fe) (p q : Spec.Ed448.Point) : Spec.Ed448.Point :=
  let a := p.Z * q.Z
  let b := a * a
  let c := p.X * q.X
  let d' := p.Y * q.Y
  let e := dd * c * d'
  let f := b - e
  let g := b + e
  let h := (p.X + p.Y) * (q.X + q.Y)
  ⟨a * f * (h - c - d'), a * g * (d' - c), f * g⟩

theorem addWith_d (p q : Spec.Ed448.Point) : addWith Spec.Ed448.d p q = Spec.Ed448.pointAdd p q := rfl

theorem doubleOps_valid : ∀ op ∈ doubleOps, fopValid op := by decide
theorem addOps_valid : ∀ op ∈ addOps, fopValid op := by decide

theorem doubleOps_eval (e : Env) :
    pt (evalOps doubleOps e) 0 1 2 = Proof.Ed448.double (pt e 0 1 2) := rfl

theorem addOps_eval (e : Env) :
    pt (evalOps addOps e) 3 4 5 = addWith (e 11) (pt e 0 1 2) (pt e 8 9 10) := rfl

def fopDest : FOp → Nat
  | .mul o _ _ | .sqr o _ | .add o _ _ | .sub o _ _ => o

theorem evalOps_keep (ops : List FOp) (e : Env) (i : Index)
    (hi : ∀ op ∈ ops, fopDest op % 22 ≠ i.val) : evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    change evalOps ops (evalOp op e) i = e i
    rw [ih _ fun o h => hi o (List.mem_cons_of_mem _ h)]
    have h := hi op List.mem_cons_self
    have hne : i ≠ idx (fopDest op) := fun h' => h (by rw [h']; rfl)
    cases op <;> simp only [evalOp, opMul, opAdd, opSub] <;> exact Function.update_of_ne hne _ _

theorem doubleOps_keep (e : Env) (i : Index) (hi : 3 ≤ i.val ∧ i.val < 12 ∨ i.val = 20 ∨ i.val = 21) :
    evalOps doubleOps e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleOps, fopDest op < 3 ∨ (12 ≤ fopDest op ∧ fopDest op < 20) := by decide
    have := this op hop
    omega

theorem addOps_keep (e : Env) (i : Index) (hi : i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21) :
    evalOps addOps e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ addOps, (3 ≤ fopDest op ∧ fopDest op < 6) ∨ (12 ≤ fopDest op ∧ fopDest op < 21) := by decide
    have := this op hop
    omega

end VG.Proof.Ed448.X86_64
