import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on x86-64: tables of constants in the working space

Untrusted: everything here is checked by Lean. `storeTab t n` leaves the
`u32`s `t 0, …, t (n - 1)` at `r9` (`Tab`), and writes nothing else
(`storeTab_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The first `n` entries of the table `t` are the `u32`s at `p`. -/
def Tab (t : Nat → Nat) (m : Mem) (p : Addr) (n : Nat) : Prop :=
  ∀ k < n, coeffAt m p k = BitVec.ofNat 32 (t k)

theorem tabStep_ok (t : Nat → Nat) (i : Nat) (s : State)
    (hw : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (tabStep t i)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r9 + BitVec.ofNat 64 (4 * i)) (BitVec.ofNat 32 (t i)) ∧
        Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold tabStep
  xrun [hw]

/-- The table, stored in the 1024 bytes at `r9`. -/
theorem storeTab_ok (t : Nat → Nat) {n : Nat} (hn : n ≤ 256) (s : State)
    (hw : pR (s.gpr .r9) ∈ s.wr) :
    WP isa (.block (storeTab t n)) s fun s' =>
      Tab t s'.mem (s.gpr .r9) n ∧ Frame [pR (s.gpr .r9)] s.mem s'.mem ∧ Keep [.rax] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [.rax] s s' ∧
      Frame [pR (s.gpr .r9)] s.mem s'.mem ∧ Tab t s'.mem (s.gpr .r9) k)
    (fun k s' hk ⟨hk', hf, ht⟩ => ?_) n (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, ht⟩ => ⟨ht, hf, hk⟩
  have h9 : s'.gpr .r9 = s.gpr .r9 := hk'.gpr (by decide)
  refine WP.mono (tabStep_ok t k s' (by
      rw [hk'.2.2, h9]; exact ⟨_, hw, coeff_contains _ (show k < 256 by omega)⟩))
    fun s'' ⟨hm', hk''⟩ => ⟨(hk'.trans hk'').mono (by decide), ?_, fun j hj => ?_⟩
  · rw [hm', h9]
    exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show k < 256 by omega))
  · rw [hm', h9, ← coeffAddr, coeffAt_writeW _ _ (show j < 256 by omega) (show k < 256 by omega)]
    by_cases e : k = j
    · subst e; rw [ifp rfl]
    · rw [ifn e]; exact ht j (by omega)

/-- Writes elsewhere keep the table. -/
theorem Tab.frame {t : Nat → Nat} {m m' : Mem} {p : Addr} {n : Nat} (h : Tab t m p n) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (pR p).Disjoint r) (hn : n ≤ 256) : Tab t m' p n :=
  fun k hk => by rw [coeffAt_congr (bytes_frame hf hd (by decide)) (show k < 256 by omega)]; exact h k hk

end VG.Proof.MlKem.X86_64
