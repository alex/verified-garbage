import VerifiedGarbage.Spec.Argon2

/-! # Facts about Argon2's block permutation -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

/-- The four output words of GB in register order. -/
def mix (va vb vc vd : Word) : Word × Word × Word × Word :=
  let a := addMul va vb
  let d := (vd ^^^ a).rotateRight 32
  let c := addMul vc d
  let b := (vb ^^^ c).rotateRight 24
  let a := addMul a b
  let d := (d ^^^ a).rotateRight 16
  let c := addMul c d
  let b := (b ^^^ c).rotateRight 63
  (a, b, c, d)

/-- The register result written to four selected vector positions. -/
def mixWords {n : Nat} (v : Vector Word n) (a b c d : Fin n) : Vector Word n :=
  let x := mix v[a] v[b] v[c] v[d]
  (((v.set a x.1).set b x.2.1).set c x.2.2.1).set d x.2.2.2

/-- Restrict a block to the sixteen words of a row or column. -/
def gather (index : Fin 16 → Fin 128) (v : Block) : Vector Word 16 :=
  Vector.ofFn fun i => v[(index i).val]'(index i).isLt

theorem gather_get (index : Fin 16 → Fin 128) (v : Block) (j : Fin 16) :
    (gather index v)[j] = v[index j] := by
  simp only [gather, Fin.getElem_fin, Vector.getElem_ofFn]

/-- An update through an injective row/column map updates exactly one gathered word. -/
theorem gather_set (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (v : Block) (a : Fin 16) (x : Word) :
    gather index (v.set (index a) x) = (gather index v).set a x := by
  apply Vector.ext
  intro j hj
  change (gather index (v.set (index a) x))[(⟨j, hj⟩ : Fin 16)] =
    ((gather index v).set a x)[j]
  rw [gather_get]
  simp only [Fin.getElem_fin, Vector.getElem_set]
  have hg : (gather index v)[j] = v[index ⟨j, hj⟩] := gather_get index v ⟨j, hj⟩
  rw [hg]
  have he : (index a).val = (index ⟨j, hj⟩).val ↔ a.val = j := by
    constructor
    · intro h
      exact congrArg Fin.val (hi (Fin.ext h))
    · intro h
      exact congrArg (fun k => (index k).val) (Fin.ext h)
  simp only [he, Fin.getElem_fin]

theorem set_get (v : Vector Word 16) (a : Fin 16) (x : Word) (k : Nat) (hk : k < 16) :
    (v.set a x)[k] = if a.1 = k then x else v[k] := by
  simp [Vector.getElem_set]

theorem set_get_fin (v : Vector Word 16) (a b : Fin 16) (x : Word) :
    (v.set a x)[b] = if a.1 = b.1 then x else v[b] := by
  simp [Vector.getElem_set]

/-- Word `k` after `G` on four distinct words. -/
theorem GB_get (v : Vector Word 16) {a b c d : Fin 16} (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1)
    (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1)
    (k : Nat) (hk : k < 16) :
    (GB v a b c d)[k] =
      if b.1 = k then (mix v[a] v[b] v[c] v[d]).2.1
      else if c.1 = k then (mix v[a] v[b] v[c] v[d]).2.2.1
      else if d.1 = k then (mix v[a] v[b] v[c] v[d]).2.2.2
      else if a.1 = k then (mix v[a] v[b] v[c] v[d]).1 else v[k] := by
  simp only [GB, set_get, set_get_fin, hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac,
    Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd, ite_true, ite_false]
  by_cases eb : b.1 = k
  · subst eb; simp only [ite_true, hab, hbc.symm, hbd.symm, ite_false, mix]
  by_cases ec : c.1 = k
  · subst ec; simp only [ite_true, eb, hac, hcd.symm, ite_false, mix]
  by_cases ed : d.1 = k
  · subst ed; simp only [ite_true, eb, ec, had, ite_false, mix]
  by_cases ea : a.1 = k
  · subst ea; simp only [ite_true, eb, ec, ed, ite_false, mix]
  simp only [eb, ec, ed, ea, ite_false]

/-- The four-update form is the RFC's GB on distinct indices. -/
theorem GB_eq_mixWords (v : Vector Word 16) {a b c d : Fin 16}
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    GB v a b c d = mixWords v a b c d := by
  apply Vector.ext
  intro j hj
  rw [GB_get v hab hac had hbc hbd hcd j hj]
  simp only [mixWords, Vector.getElem_set]
  by_cases hdj : d.val = j
  · subst j
    simp only [had, hbd, hcd, ite_true, ite_false]
  by_cases hcj : c.val = j
  · subst j
    simp only [hac, hbc, hdj, ite_true, ite_false]
  by_cases hbj : b.val = j
  · subst j
    simp only [hab, hcj, hdj, ite_true, ite_false]
  simp only [hdj, hcj, hbj, ite_false]

theorem gather_mixWords (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (v : Block) (a b c d : Fin 16) :
    gather index (mixWords v (index a) (index b) (index c) (index d)) =
      mixWords (gather index v) a b c d := by
  unfold mixWords
  rw [gather_set index hi, gather_set index hi, gather_set index hi, gather_set index hi]
  simp only [gather_get]

end VG.Proof.Argon2
