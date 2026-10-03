import VerifiedGarbage.Proof.Argon2.AArch64.Finish
import VerifiedGarbage.Proof.Argon2.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Argon2.AArch64.Words

/-! Merged from `Proof.Argon2.AArch64.Round`. -/
section
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
end

/-! Correctness, memory safety, ABI preservation, and constant time of ARM64 Argon2 G. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64 VG.Spec.Argon2

theorem original_preserved {m m' : Mem} {p : Addr}
    (hf : Frame [⟨off p 1024, 1024⟩] m m') : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  have he : m'.readW (off p (8 * i)) 64 = m.readW (off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega) (by omega))
      (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact Offset.base_disjoint p (by decide) (by decide)) (by decide)
  rw [← blockAt_get m' p ⟨i, hi⟩, ← blockAt_get m p ⟨i, hi⟩] at he
  exact he

theorem round_frame {m m' : Mem} {p out : Addr}
    (hf : Frame [⟨off p 1024, 1024⟩] m m') : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨p, 4096⟩, by simp, Offset.sub_base p (by decide)⟩

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.AArch64.compress s fun t => compressLocal.post s t := by
  obtain ⟨hrd, hwr, hout, hx, hy⟩ := hs
  have scr : Scratch s (s.gpr .x3) := ⟨rfl, by simp [hwr]⟩
  have inputs : Inputs s (s.gpr .x0) (s.gpr .x1) (s.gpr .x3) :=
    ⟨rfl, rfl, by simp [hrd], by simp [hrd], hx, hy⟩
  unfold Impl.Argon2.AArch64.compress
  apply WP.seq
  refine (init_prefix 128 (by decide) s scr inputs).mono ?_
  rintro s1 ⟨hinit, _hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := initialized_blocks hinit
  have scr1 := scr.of_copy hk1
  apply WP.seq
  refine (rounds_ok rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8) s1 scr1).mono ?_
  rintro s2 ⟨hrow, hf2, hk2⟩
  apply WP.seq
  refine (rounds_ok colIndex Proof.Argon2.colIndex_injective (List.finRange 8)
    s2 (scr1.of_keeps hk2)).mono ?_
  rintro s3 ⟨hcol, hf3, hk3⟩
  have hout3 : s3.gpr .x2 = s.gpr .x2 := by
    rw [hk3.1 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hk2.1 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hk1.1 .x2 (by decide) (by decide)]
  have hw3 : s3.wr = s.wr := hk3.2.2.trans (hk2.2.2.trans hk1.2.2)
  refine (finish_prefix 128 (by decide) s3 ((scr1.of_keeps hk2).of_keeps hk3) hout3
    (by rw [hw3, hwr]; simp) hout.symm).mono ?_
  rintro t ⟨hfinish, _hf4, _hk4⟩
  have ho3 := original_preserved (hf2.trans hf3)
  rw [horig] at ho3
  have he := written_block hfinish
  rw [hcol, hrow, hwork, ho3] at he
  exact he

theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.AArch64.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp⟩ := compress_wp s hs
  refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, hp⟩
  intro r hr
  apply Exec.gpr (c := Impl.Argon2.AArch64.compress) (hn := .inl (by decide +kernel)) _ he
  have hk : Impl.Argon2.AArch64.compress.allInstrs (keeps (RegSet.ofList preserved)) = true := by
    lit_decide
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (instrs_keeps hk) i hi) r hr
  simpa only [bne_iff_ne] using h

theorem compress_verified : Verified AArch64.target Impl.Argon2.AArch64.compress
    (Spec.Argon2.compressContract AArch64.abi) :=
  Verified.of_correct compress_correct compress_ct compress_implies
end VG.Proof.Argon2.AArch64
