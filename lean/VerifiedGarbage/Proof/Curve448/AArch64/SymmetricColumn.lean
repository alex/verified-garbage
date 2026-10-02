import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
import VerifiedGarbage.Proof.Curve448.AArch64.AccumSquareBody
/-! Untrusted: store a symmetric square diagonal. -/
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem symmetricColumn_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat} {k : Nat}
    (hk : k < 16) (fc : ∀ i < 8, (s.gpr (cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < weakBound) :
    WP isa (.block (Impl.X448.AArch64.Symmetric.column k)) s fun t =>
      coeff t.mem base ACC k = rows f f 8 k ∧
      Outside base (ACC + 16 * k) 16 s.mem t.mem ∧ Keeps termRegs s t := by
  rw [Impl.X448.AArch64.Symmetric.column, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun u ⟨uz, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have uk' : Keeps termRegs s u := uk.mono (by decide)
  refine WP.mono (accumSquareBody_ok hk (by
    intro i hi; rw [uk'.1 _ (cacheReg_kept hi)]; exact fc i hi) fb (by decide) uz)
    fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (store_ok vs hk) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, uk'.trans (vk.trans (tk.mono (by decide)))⟩
  · rw [tm, coeff_put _ base _ _ (by simp only [ACC]; omega)
      (by simp only [ACC]; omega), ite_eq_left rfl, vv, Nat.zero_add]
  · rw [tm, vm, um]
    exact putCoeff_outside _ _ _ _ (by simp only [ACC]; omega)
end VG.Proof.Curve448.AArch64
