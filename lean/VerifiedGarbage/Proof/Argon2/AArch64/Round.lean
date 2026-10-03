import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Argon2.AArch64.Words

/-! # The row and column permutations in scratch -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2
open VG.Proof.Argon2

/-- Registers and permissions preserved throughout a scratch permutation. -/
def Keeps (s t : State) : Prop :=
  (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
    r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
  t.rd = s.rd ∧ t.wr = s.wr

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ _ _ _ _ _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u :=
  ⟨fun r h8 h9 h10 h11 h0 hdx hsi =>
    (h'.1 r h8 h9 h10 h11 h0 hdx hsi).trans (h.1 r h8 h9 h10 h11 h0 hdx hsi),
    h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Scratch.of_keeps {s t : State} {p : Addr} (hs : Scratch s p)
    (hk : Keeps s t) : Scratch t p :=
  ⟨(hk.1 .x3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hs.reg, hk.2.2 ▸ hs.wr⟩

/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : Block) (v : Vector Word 16)
    (m : Mem) (p : Addr) : Prop :=
  gather index (working m p) = v ∧
  ∀ k : Fin 128, (∀ j, index j ≠ k) → (working m p)[k] = b[k]

theorem holds_self (index : Fin 16 → Fin 128) (m : Mem) (p : Addr) :
    Holds index (working m p) (gather index (working m p)) m p :=
  ⟨rfl, fun _ _ => rfl⟩

/-- One GB advances the selected row or column and preserves its complement. -/
theorem step_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : Scratch s p) (base : Block) (v : Vector Word 16)
    (hv : Holds index base v s.mem p) (a b c d : Fin 16)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.AArch64.gbAt (index a).val (index b).val (index c).val (index d).val)
      s fun t => Holds index base (GB v a b c d) t.mem p ∧
        Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  refine (gbAt_words s hs (index a) (index b) (index c) (index d)).mono ?_
  rintro t ⟨hw, hf, hk⟩
  refine ⟨⟨?_, ?_⟩, hf, hk⟩
  · rw [hw, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [hw]
    have ne (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne, ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column, with a cumulative memory frame. -/
theorem permuteAt_holds (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : Scratch s p) (base : Block) (v : Vector Word 16)
    (hv : Holds index base v s.mem p) :
    WP isa (Impl.Argon2.AArch64.permuteAt index) s fun t =>
      Holds index base (permute v) t.mem p ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  have advance (t : State) (v' : Vector Word 16)
      (h : Holds index base v' t.mem p ∧ Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.AArch64.gbAt (index a).val (index b).val (index c).val (index d).val)
        t fun u => Holds index base (GB v' a b c d) u.mem p ∧
          Frame [⟨off p 1024, 1024⟩] s.mem u.mem ∧ Keeps s u := by
    refine (step_ok index hi t (hs.of_keeps h.2.2) base v' h.1 a b c d
      hab hac had hbc hbd hcd).mono ?_
    rintro u ⟨hu, hf, hk⟩
    exact ⟨hu, h.2.1.trans hf, h.2.2.trans hk⟩
  unfold Impl.Argon2.AArch64.permuteAt
  apply WP.seq
  refine (advance s _ ⟨hv, Frame.refl _ _, Keeps.refl s⟩ 0 4 8 12
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
theorem permuteAt_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (Impl.Argon2.AArch64.permuteAt index) s fun t =>
      working t.mem p = Spec.Argon2.permuteAt index (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  refine (permuteAt_holds index hi s hs (working s.mem p)
    (gather index (working s.mem p)) (holds_self index s.mem p)).mono ?_
  rintro t ⟨ht, hf, hk⟩
  exact ⟨eq_scatter index hi _ _ _ ht.1 ht.2, hf, hk⟩

/-- Compose a list of row or column permutations without re-executing any GB proof. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128)
    (hi : ∀ i, Function.Injective (index i)) (is : List (Fin 8))
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.AArch64.permuteAt (index i)) rest)
      (.block [])) s fun t =>
      working t.mem p = is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, Keeps.refl s⟩
  | cons i is ih =>
    apply WP.seq
    refine (permuteAt_ok (index i) (hi i) s hs).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (ih t (hs.of_keeps hk)).mono ?_
    rintro u ⟨hu, hf', hk'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk'⟩
    simpa only [List.foldl_cons, ht] using hu

end VG.Proof.Argon2.AArch64
