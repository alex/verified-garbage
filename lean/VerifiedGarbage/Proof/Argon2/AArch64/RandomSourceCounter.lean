import VerifiedGarbage.Proof.Argon2.AArch64.RandomSource

/-! The stored address counter remains public after either source. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

def counterValue (p : Params) (pass slice index old : Nat) : Addr :=
  BitVec.ofNat 64 (if independent p pass slice then index / 128 + 1 else old)

theorem counter_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) :
    WP isa Impl.Argon2.AArch64.RandomSource.code s fun t =>
      t.mem.readW (off (t.gpr .x19) 8) 64 = counterValue p pass slice index old := by
  unfold Impl.Argon2.AArch64.RandomSource.code
  refine WP.seq ((prepare_ok s p pass lane slice index old h).mono ?_)
  rintro a ⟨flag, keeps⟩
  have next := h.of_keeps keeps
  refine WP.ite (!independent p pass slice) flag ?_ ?_
  · intro mode
    have dependent : independent p pass slice = false := by cases eq : independent p pass slice <;> simp_all
    refine (DependentWord.code_ok a p pass lane slice index next.filling).mono ?_
    rintro t ⟨_, saved⟩
    unfold counterValue
    simp only [dependent]
    rw [saved.mem, saved.regs .x19 (by decide)]
    exact next.cache.words.counterWord
  · intro mode
    have independent : independent p pass slice = true := by cases eq : independent p pass slice <;> simp_all
    refine (AddressCache.code_ok p pass lane slice old a next.cache.ready).mono ?_
    intro t done
    unfold counterValue
    simp only [independent, ite_true]
    rw [done.selected.counterWord, AddressCache.counter_nat, next.index_nat]

end VG.Proof.Argon2.AArch64.RandomSource
