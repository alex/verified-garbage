import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-DSA on AArch64: tables of constants in the working space

`storeTab t n b` leaves the `u32`s `t 0, …, t (n - 1)` at `b` (`Tab`), and
writes nothing else (`storeTab_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (coeffAt)

/-- The first `n` entries of the table `t` are the `u32`s at `p`. -/
def Tab (t : Nat → Nat) (m : Mem) (p : Addr) (n : Nat) : Prop :=
  ∀ k < n, coeffAt m p k = BitVec.ofNat 32 (t k)

theorem tabStep_ok (t : Nat → Nat) (b : Reg) (hb : b ≠ .x9) (i : Nat) (hi : i < 256) (s : State)
    (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (tabStep t b i)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 (4 * i)) (BitVec.ofNat 32 (t i))) ∧
        Keep [.x9] s s' := by
  unfold tabStep
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok .x9 _ s) fun s₁ ⟨⟨h9, hm⟩, k₁⟩ => ?_
  have hb' : s₁.gpr b = s.gpr b := k₁.get b (by simpa using hb)
  have ho : 4 * i % 4 = 0 ∧ 4 * i < 16384 := ⟨by omega, by omega⟩
  have hw₁ : InRegions s₁.wr (s₁.gpr b + BitVec.ofNat 64 (4 * i)) 4 := by rw [k₁.wr, hb']; exact hw
  refine WP.mono (WP.keep (c := .block [Instr.str .w .x9 b (4 * i)]) (s := s₁) []
    (Q := fun s' => s'.mem = s₁.mem.writeW (s₁.gpr b + BitVec.ofNat 64 (4 * i)) ((s₁.gpr .x9).setWidth 32))
    (by arun [ho, hw₁]) (by rfl) (hv := rfl)) fun s₂ ⟨hm₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono⟩
  rw [hm₂, hb', hm, h9, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- The table, stored in the 1024 bytes at `b`. -/
theorem storeTab_ok (t : Nat → Nat) {b : Reg} (hb : b ≠ .x9) (s : State) (hw : pR (s.gpr b) ∈ s.wr) :
    WP isa (.block (storeTab t 256 b)) s fun s' =>
      Tab t s'.mem (s.gpr b) 256 ∧ Frame [pR (s.gpr b)] s.mem s'.mem ∧ Keep [.x9] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [.x9] s s' ∧
      Frame [pR (s.gpr b)] s.mem s'.mem ∧ Tab t s'.mem (s.gpr b) k)
    (fun k s' hk ⟨hk', hf, ht⟩ => ?_) 256 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, ht⟩ => ⟨ht, hf, hk⟩
  have hb' : s'.gpr b = s.gpr b := hk'.get b (by simpa using hb)
  refine WP.mono (tabStep_ok t b hb k hk s' (by
      rw [hk'.wr, hb']; exact ⟨_, hw, coeff_contains _ (show k < 256 by omega)⟩))
    fun s'' ⟨hm', hk''⟩ => ⟨(hk'.trans hk'').mono, ?_, fun j hj => ?_⟩
  · rw [hm', hb']
    exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show k < 256 by omega))
  · rw [hm', hb', ← coeffAddr, coeffAt_writeW _ _ (show j < 256 by omega) (show k < 256 by omega)]
    by_cases e : k = j
    · subst e; rw [ite_eq_left rfl]
    · rw [ite_eq_right e]; exact ht j (by omega)

/-- Writes elsewhere keep the table. -/
theorem Tab.frame {t : Nat → Nat} {m m' : Mem} {p : Addr} {n : Nat} (h : Tab t m p n) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (pR p).Disjoint r) (hn : n ≤ 256) : Tab t m' p n :=
  fun k hk => by rw [coeffAt_frame hf hd (show k < 256 by omega)]; exact h k hk

end VG.Proof.MlDsa.AArch64.Arith
