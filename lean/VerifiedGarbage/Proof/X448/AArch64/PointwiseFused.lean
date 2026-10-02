import VerifiedGarbage.Proof.X448.AArch64.PointwiseCarry
import VerifiedGarbage.Proof.X448.AArch64.PointwiseFinish
import VerifiedGarbage.Proof.X448.AArch64.Columns

/-! Untrusted: fuse a pointwise coefficient with its first carry step. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem pointwiseFirst_ok {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {f : Nat → Nat} (hb : ∀ i < 16, f i < 2 ^ 62)
    (heval : ∀ i < 16, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        u.gpr .x4 = BitVec.ofNat 64 (f i) ∧ u.mem = t.mem ∧ Keeps [.x4, .x5] t u) :
    WP isa (.block (([.movz .x .x6 0 0] : List Instr) ++
      (List.range 16).flatMap (fun i => code i ++ Pointwise.carry i))) s fun t =>
      (∀ i < 16, limbs t.mem base TMP i = digit f i) ∧
      (t.gpr .x6).toNat = carry f 16 ∧ Outside base TMP 128 s.mem t.mem ∧
      Keeps [.x4, .x6, .x5] s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, limbs t.mem base TMP i = digit f i) ∧
    (t.gpr .x6).toNat = carry f k ∧ Outside base TMP 128 s.mem t.mem ∧
    Keeps [.x4, .x6, .x5] s t
  have step : ∀ k t, k < 16 → inv k t →
      WP isa (.block (code k ++ Pointwise.carry k)) t (inv (k + 1)) := by
    intro k t hk ⟨tf, tc, tm, tk⟩
    rw [WP.block_append_iff]
    refine WP.mono (heval k hk t (hs.of_keeps tk (by decide)) tm) fun u ⟨uv, um, uk⟩ => ?_
    have uc : (u.gpr .x6).toNat = carry f k := by rw [uk.1 .x6 (by decide), tc]
    have u4 : (u.gpr .x4).toNat = f k := by
      rw [uv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (hb k hk) (by decide))]
    have cap : (u.gpr .x4).toNat + (u.gpr .x6).toNat < 2 ^ 64 := by
      rw [u4, uc]
      have c := carry_bound (n := k) (fun i hi => hb i (by omega))
      have h := hb k hk
      omega
    have us := (hs.of_keeps tk (by decide)).of_keeps uk (by decide)
    refine WP.mono (pointwiseCarry_ok us hk cap) fun v ⟨vc, vm, vk⟩ => ?_
    rw [u4, uc] at vc vm
    have out : Outside base (TMP + 8 * k) 8 t.mem v.mem := by
      rw [vm, um]; exact writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, vc, tm.trans (out.mono (by omega) (by omega)),
      tk.trans ((uk.mono (by decide)).trans vk)⟩
    intro i hi
    change (word v.mem base (TMP + 8 * i)).toNat = _
    rw [vm, um, word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat]
      change digit f k % 2 ^ 64 = digit f k
      exact Nat.mod_eq_of_lt (Nat.lt_trans (digit_lt f k) (by decide : radix < 2 ^ 64))
    · rw [ite_eq_right h]; exact tf i (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (zeroCarry_ok s) fun u ⟨uc, um, uk⟩ => ?_
  exact wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) u
    ⟨fun _ hi => by omega, by rw [uc]; rfl, by rw [um]; exact Outside.refl _ _ _ _, uk⟩

theorem pointwiseFused_ok {s : State} {base : Addr} (hs : Scr s base)
    {code : Nat → List Instr} {o : Nat} (ho : Slot o) (ho8 : o % 8 = 0)
    {f : Nat → Nat} (hb : ∀ i < 16, f i < 2 ^ 62)
    (heval : ∀ i < 16, ∀ t, Scr t base → Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        u.gpr .x4 = BitVec.ofNat 64 (f i) ∧ u.mem = t.mem ∧ Keeps [.x4, .x5] t u) :
    WP isa (.block (Pointwise.fused code o)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧
      fe t.mem base o % Spec.X448.P = valN f 16 % Spec.X448.P := by
  rw [Pointwise.fused, WP.block_append_iff]
  refine WP.mono (pointwiseFirst_ok hs hb heval) fun u ⟨uf, uc, um, uk⟩ => ?_
  refine WP.mono (pointwiseFinish_ok (hs.of_keeps uk (by decide)) ho ho8 uf uc hb)
    fun t ⟨tf, tm, tk⟩ => ?_
  refine ⟨⟨(uk.mono (by decide)).trans (tk.mono (by decide)),
    (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
  · intro i hi; rw [tf i hi]; exact digit_lt _ _
  · rw [show fe t.mem base o = valN (normalized f) 16 from valN_congr tf, normalized_mod hb]

end VG.Proof.X448.AArch64
