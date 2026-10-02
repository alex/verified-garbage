import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge

/-!
# ML-DSA on AArch64: the output polynomial set to zeros

`zeroPoly` stores zero to the 256 coefficients of the output polynomial
(`zeroPoly_ok`), and writes nothing else but `x3`, `x4` and `x9`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_addImm wp_subImm wp_strw ptr_zero
  toNat_sub_n count_loop)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample (coeffAddr polyR coeff_contains coeffAt_writeW)
open VG.Spec.MlDsa (coeffAt)

/-- After `k` coefficients set to zero. -/
structure ZInv (aP : Addr) (s₁ : State) (k : Nat) (u : State) : Prop where
  keep : Keep [.x3, .x4] s₁ u
  x3 : u.gpr .x3 = coeffAddr aP k
  x4 : (u.gpr .x4).toNat = 256 - k
  zero : ∀ i < k, coeffAt u.mem aP i = 0
  frame : Frame [polyR aP] s₁.mem u.mem

theorem zero_step {aP : Addr} {s₁ : State} (hw : ∀ i < 256, InRegions s₁.wr (coeffAddr aP i) 4)
    (h9 : s₁.gpr .x9 = 0) {k : Nat} (hk : k < 256) {u : State} (h : ZInv aP s₁ k u) :
    WP isa (.block [.str .w .x9 .x3 0, .addImm .x .x3 .x3 4, .subImm .x .x4 .x4 1]) u
      fun u' => ZInv aP s₁ (k + 1) u' ∧ ((u'.gpr .x4).toNat ≠ 0 ↔ k + 1 ≠ 256) := by
  refine wp_strw (a := coeffAddr aP k) (by decide) (by rw [h.x3, ptr_zero]) (by rw [h.keep.wr]; exact hw k hk)
    fun u₁ h₁ => wp_addImm (by decide) fun u₂ h₂ e₂ => wp_subImm (by decide) fun u₃ h₃ e₃ => wp_nil ?_
  have c4 : (u₂.gpr .x4).toNat = 256 - k := by rw [h₂.get .x4, h₁.gpr, h.x4]
  have v4 : (u₃.gpr .x4).toNat = 256 - (k + 1) := by
    rw [e₃, toNat_sub_n (by rw [c4]; simp; omega), c4]
    simp
    omega
  have m₃ : u₃.mem = u.mem.writeW (coeffAddr aP k) ((u.gpr .x9).setWidth 32) := by
    rw [h₃.mem, h₂.mem, h₁.mem]
  have z : (u.gpr .x9).setWidth 32 = 0 := by rw [h.keep.get .x9, h9]; rfl
  refine ⟨⟨(h.keep.trans ((h₁.keep.trans h₂.keep).trans h₃.keep)).mono, ?_, v4, fun i hi => ?_, ?_⟩,
    by rw [v4]; omega⟩
  · rw [h₃.get .x3, e₂, h₁.gpr, h.x3, coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [m₃, z, coeffAt_writeW _ _ (by omega) hk]
    split
    · rfl
    · exact h.zero i (by omega)
  · rw [m₃]
    exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk)

/-- The coefficients of `a` set to zeros. -/
theorem zeroPoly_ok {aP : Addr} {s : State} (hw : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4)
    (h26 : s.gpr .x26 = aP) :
    WP isa zeroPoly s fun u => Keep [.x9, .x3, .x4] s u ∧ (∀ i < 256, coeffAt u.mem aP i = 0) ∧
      Frame [polyR aP] s.mem u.mem := by
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_nil ?_)
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have z9 : s₃.gpr .x9 = 0 := by rw [h₃.get .x9, h₂.get .x9, e₁]; rfl
  have i₀ : ZInv aP s₃ 0 s₃ := ⟨Keep.refl _ _,
    by rw [h₃.get .x3, e₂, h₁.get .x26, h26, coeffAddr, Nat.mul_zero, ptr_zero],
    by rw [e₃]; rfl, fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  refine WP.mono (count_loop (by decide) (ZInv aP s₃)
    (fun k hk u hu => zero_step (by rw [k₃.wr]; exact hw) z9 hk hu) i₀) fun s₄ h₄ => ?_
  refine ⟨(k₃.trans h₄.keep).mono, h₄.zero, ?_⟩
  rw [← show s₃.mem = s.mem by rw [h₃.mem, h₂.mem, h₁.mem]]
  exact h₄.frame

end VG.Proof.MlDsa.AArch64.Sample
