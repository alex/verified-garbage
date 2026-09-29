import VerifiedGarbage.Impl.MlKem.X86_64.Sample
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Stream

/-!
# ML-KEM on x86-64: zeroing a Keccak state

Untrusted: everything here is checked by Lean. `zeroSt b off` stores `rax`
(zero) to the 25 lanes at `b + off`: the all-zero state (`zeroSt_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem lane_sep (p : Addr) {i j : Nat} (hi : i < 25) (hj : j < 25) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (8 * i)) (64 / 8) (p + BitVec.ofNat 64 (8 * j)) (64 / 8) := by
  intro x hx hy
  simp only [Nat.reduceDiv] at hx hy
  bv_omega

theorem zeroStep_ok (b : Reg) (d : Nat) (s : State) (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.store (at_ b d) .rax]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 d) (s.gpr .rax)) ∧ Keep [] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [hw]

/-- The lanes at `b + off`, zeroed. -/
theorem zeroSt_ok (b : Reg) (off : Nat) (s : State) (h0 : s.gpr .rax = 0)
    (hw : ∀ i < 25, InRegions s.wr (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (zeroSt b off)) s fun s' =>
      Spec.Sha3.stateAt s'.mem (s.gpr b + BitVec.ofNat 64 off) = Spec.Sha3.zero ∧
        Frame [⟨s.gpr b + BitVec.ofNat 64 off, 200⟩] s.mem s'.mem ∧ Keep [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [] s s' ∧
      Frame [⟨s.gpr b + BitVec.ofNat 64 off, 200⟩] s.mem s'.mem ∧
      ∀ j < k, s'.mem.readW (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * j)) 64 = 0)
    (fun k s' hk ⟨hk', hf, hz⟩ => ?_) 25 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, hz⟩ => ⟨?_, hf, hk⟩
  · have hb : s'.gpr b = s.gpr b := hk'.gpr (by simp)
    have ha : s'.gpr .rax = 0 := by rw [hk'.gpr (by simp), h0]
    have e : s.gpr b + BitVec.ofNat 64 (off + 8 * k) = s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    refine WP.mono (zeroStep_ok b (off + 8 * k) s' (by rw [hk'.2.2, hb, e]; exact hw k hk))
      fun s'' ⟨hm, hk''⟩ => ⟨hk'.trans hk'', ?_, fun j hj => ?_⟩
    · rw [hm, hb, e]
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
    · rw [hm, hb, e, ha]
      by_cases hjk : j = k
      · subst hjk; rw [Mem.readW_writeW_self64]
      · rw [Mem.readW_writeW_sep (lane_sep _ (by omega) hk hjk) (by decide), hz j (by omega)]
  · apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact hz i hi

end VG.Proof.MlKem.X86_64
