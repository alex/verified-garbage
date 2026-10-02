import VerifiedGarbage.Impl.Ed25519.X86.PointLoop
import VerifiedGarbage.Proof.Ed25519.X86.Points
import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Ed25519.ScalarMul

/-! Fixed-size batches of powers use exactly the specified point formula. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem doubleBody_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat}
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hb : s.gpr .esi = BitVec.ofNat 32 n)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (.block doubleBody) s fun t =>
      IKeep x s t ∧ t.gpr .esi = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne t = some (!decide (n - 1 = 0)) ∧
      point (env t.mem x) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem x) 0 1 2 3) (point (env s.mem x) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  rw [doubleBody, WP.block_append_iff]
  refine WP.mono (pointDouble_ok hc hd) fun t ⟨ht, pt, high⟩ => ?_
  refine Wp.wp_subi fun u hu _ hz => WP.block_nil ?_
  refine ⟨(IKeep.of_field ht).trans (IKeep.of_counter hu), ?_, ?_, ?_, ?_⟩
  · rw [hu.gpr, ht.keep.esi, hb]; exact Wp.ofNat_pred hn
  · show u.zf.map (!·) = _
    rw [hz, ht.keep.esi, hb, Wp.ofNat_pred hn, Wp.ofNat_beq_zero (by omega_using [hn'])]
    rfl
  · rw [hu.mem]; exact pt
  · rw [hu.mem]; exact high

structure DoubleInv (x : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  lo : 1 ≤ n
  hi : n ≤ 16
  keep : IKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = powerPoint (point (env s₀.mem x) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem x i = env s₀.mem x i

theorem double16_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa double16 s fun t => IKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = powerPoint (point (env s.mem x) 0 1 2 3) 16 ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.seq (Wp.wp_movi fun t ht => WP.block_nil ?_)
  refine WP.loop (M := isa) (Inv := DoubleInv x s) ?_ 16 t
    ⟨by decide, by decide, IKeep.of_counter ht, ht.gpr, ?_, ?_⟩
  · intro n u h
    have du : env u.mem x 16 = Spec.Ed25519.d := (h.high 16 (by decide)).trans hd
    refine WP.mono (doubleBody_ok (h.keep.ctx hc) h.lo (by omega_using [h.hi]) h.counter du)
      fun v ⟨kv, bv, zv, pv, high⟩ => ?_
    have kk := h.keep.trans kv
    have pp : point (env v.mem x) 0 1 2 3 =
        powerPoint (point (env s.mem x) 0 1 2 3) (16 - (n - 1)) := by
      exact pv.trans ((congrArg₂ Spec.Ed25519.pointAdd h.value h.value).trans
        (by rw [show 16 - (n - 1) = (16 - n) + 1 by omega_using [h.lo, h.hi]]; rfl))
    have hh : ∀ i : Slot, 16 ≤ i.val → env v.mem x i = env s.mem x i :=
      fun i hi => (high i hi).trans (h.high i hi)
    by_cases hn : n = 1
    · subst n
      exact .inl ⟨by rw [zv]; rfl, kk, pp, hh⟩
    · exact .inr ⟨by rw [zv]; simp only [show n - 1 ≠ 0 by omega_using [hn, h.lo], decide_false]; rfl,
        n - 1, by omega_using [h.lo], by omega_using [hn, h.lo], by omega_using [h.hi], kk, bv, pp, hh⟩
  · rw [ht.mem]; rfl
  · rw [ht.mem]; exact fun _ _ => rfl

end VG.Proof.Ed25519.X86
