import VerifiedGarbage.Proof.Argon2.AArch64.Memory

/-! # The scratch block as a vector of words -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2

/-- The permuted half of scratch. -/
def working (m : Mem) (p : Addr) : Block := Vector.ofFn fun i => word m p i.val

theorem working_get (m : Mem) (p : Addr) (i : Fin 128) :
    (working m p)[i] = word m p i.val := by
  simp only [working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- A write changes exactly the selected word of the block. -/
theorem working_write (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    working (m.writeW (off p (1024 + 8 * i.val)) v) p = (working m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true, word, Mem.readW_writeW_self64]
  · simp only [h, ite_false, word]
    exact Mem.readW_writeW_sep
      (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem working_storeMix (m : Mem) (p : Addr) (a b c d : Fin 128)
    (v : Word × Word × Word × Word) :
    working (storeMix m p a.val b.val c.val d.val v) p =
      ((((working m p).set a v.1).set b v.2.1).set c v.2.2.1).set d v.2.2.2 := by
  simp only [storeMix, working_write]

theorem storeMix_frame (m : Mem) (p : Addr) (a b c d : Fin 128)
    (v : Word × Word × Word × Word) :
    Frame [⟨off p 1024, 1024⟩] m (storeMix m p a.val b.val c.val d.val v) := by
  have inside (i : Fin 128) :
      (⟨off p 1024, 1024⟩ : Region).Contains (off p (1024 + 8 * i.val)) 8 := by
    exact Offset.contains p (by omega) (by omega) (by omega)
  exact ((((Frame.refl [⟨off p 1024, 1024⟩] m).writeW (by simp) v.1 (inside a)).writeW
    (by simp) v.2.1 (inside b)).writeW (by simp) v.2.2.1 (inside c)).writeW
    (by simp) v.2.2.2 (inside d)

/-- GB updates the block vector and only the permuted half of scratch. -/
theorem gbAt_words (s : State) {p : Addr} (hs : Scratch s p) (a b c d : Fin 128) :
    WP isa (Impl.Argon2.AArch64.gbAt a.val b.val c.val d.val) s fun t =>
      working t.mem p = Proof.Argon2.mixWords (working s.mem p) a b c d ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
        r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  refine (gbAt_ok s hs a.isLt b.isLt c.isLt d.isLt).mono ?_
  rintro t ⟨hm, hk, hr, hw⟩
  refine ⟨?_, ?_, hk, hr, hw⟩
  · rw [hm, working_storeMix]
    simp only [Proof.Argon2.mixWords, working_get]
  · rw [hm]
    exact storeMix_frame s.mem p a b c d _

end VG.Proof.Argon2.AArch64
