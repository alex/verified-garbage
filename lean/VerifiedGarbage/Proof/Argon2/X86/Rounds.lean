import VerifiedGarbage.Proof.Argon2.X86.Gb
import VerifiedGarbage.Proof.Argon2.Permutation

/-!
# Argon2 on x86 (32-bit): the row and column permutations

As on x86-64 (`Proof/Argon2/X86_64/Compress.lean`): P on any injectively
selected row or column (`permuteAt_ok`), and the rows and columns
(`rounds_ok`).
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Proof.Argon2
open VG.Proof.Sha512.X86 (Acc)


/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : Block) (v : Vector Word 16) (m : Mem)
    (B : BitVec 32) : Prop :=
  gather index (working m B) = v ∧ ∀ k : Fin 128, (∀ j, index j ≠ k) → (working m B)[k] = b[k]

/-- The base and the permissions of `scratch`, and the rest of a `Step`. -/
def At (B : BitVec 32) (s : State) : Prop := s.gpr .esi = B ∧ Acc s.wr B 4096

theorem At.of_step {B : BitVec 32} {s t : State} {v : Block} (h : At B s) (st : Step B s v t) : At B t :=
  ⟨st.keep.esi.trans h.1, st.keep.wr ▸ h.2⟩

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)

include hfit

/-- One GB advances the selected row or column and preserves its complement. -/
theorem step_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : State}
    (hs : At B s) (base : Block) (v : Vector Word 16) (hv : Holds index base v s.mem B)
    (a b c d : Fin 16) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.X86.gbAt (index a).val (index b).val (index c).val (index d).val) s
      fun t => Holds index base (GB v a b c d) t.mem B ∧
        ∃ w, Step B s w t := by
  have ne : ∀ {x y : Fin 16}, x.val ≠ y.val → (index x).val ≠ (index y).val :=
    fun h e => h (congrArg Fin.val (hi (Fin.ext e)))
  refine (gbAt_ok hfit hs.1 hs.2 (index a) (index b) (index c) (index d)).mono fun t st => ?_
  rw [gbV_eq _ (ne hab) (ne hac) (ne had) (ne hbc) (ne hbd) (ne hcd)] at st
  refine ⟨⟨?_, ?_⟩, _, st⟩
  · rw [st.working, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [st.working]
    have ne' (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne', ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column. -/
theorem permuteAt_holds (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : State}
    (hs : At B s) (base : Block) (v : Vector Word 16) (hv : Holds index base v s.mem B) :
    WP isa (Impl.Argon2.X86.permuteAt index) s fun t =>
      Holds index base (permute v) t.mem B ∧ ∃ w, Step B s w t := by
  have advance (t : State) (v' : Vector Word 16)
      (h : Holds index base v' t.mem B ∧ ∃ w, Step B s w t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.X86.gbAt (index a).val (index b).val (index c).val (index d).val)
        t fun u => Holds index base (GB v' a b c d) u.mem B ∧ ∃ w, Step B s w u := by
    obtain ⟨hh, w, st⟩ := h
    refine (step_ok hfit index hi (hs.of_step st) base v' hh a b c d
      hab hac had hbc hbd hcd).mono ?_
    rintro u ⟨hu, w', st'⟩
    exact ⟨hu, w', st.trans st'⟩
  unfold Impl.Argon2.X86.permuteAt
  apply WP.seq
  refine (advance s _ ⟨hv, _, ⟨.refl s, rfl, Frame.refl _ _⟩⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : State}
    (hs : At B s) :
    WP isa (Impl.Argon2.X86.permuteAt index) s
      (Step B s (Spec.Argon2.permuteAt index (working s.mem B))) := by
  refine (permuteAt_holds hfit index hi hs (working s.mem B)
    (gather index (working s.mem B)) ⟨rfl, fun _ _ => rfl⟩).mono ?_
  rintro t ⟨ht, w, st⟩
  exact ⟨st.keep, eq_scatter index hi _ _ _ ht.1 ht.2, st.frame⟩

/-- A list of row or column permutations. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128)
    (hi : ∀ i, Function.Injective (index i)) (is : List (Fin 8)) {s : State} (hs : At B s) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.X86.permuteAt (index i)) rest)
      (.block [])) s
      (Step B s (is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (working s.mem B))) := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨.refl s, rfl, Frame.refl _ _⟩
  | cons i is ih =>
    apply WP.seq
    refine (permuteAt_ok hfit (index i) (hi i) hs).mono ?_
    intro t st
    refine (ih (hs.of_step st)).mono ?_
    intro u st'
    refine st.trans ?_
    rw [List.foldl_cons, ← st.working]
    exact st'

end

end VG.Proof.Argon2.X86
