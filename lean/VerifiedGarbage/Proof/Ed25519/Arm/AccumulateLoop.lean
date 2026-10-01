import VerifiedGarbage.Proof.Ed25519.Arm.AccumulateStep

/-! Untrusted: the descending sixteen-bit loop follows the specification exactly. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure AccumulateInv (s₀ : State) (b : BitVec 32) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  ctx : Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r11 = BitVec.ofNat 32 n
  d : env s.mem b 16 = Spec.Ed25519.d
  value : point (env s.mem b) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
    BitVec.ofNat 8 (scalarBit scalar (start + i)).toNat
  table : ∀ i < 16, tablePoint s.mem b (5696 + 128 * i) = powerPoint p (start + i)
  keep : LoopKeep b s₀ s

theorem accumulateLoop_ok {s₀ : State} {b : BitVec 32} (hc : Ctx b s₀) (hl : AllLim s₀.mem b)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (h11 : s₀.gpr .r11 = 16)
    (hb : ∀ i < 16, s₀.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
      BitVec.ofNat 8 (scalarBit scalar (start + i)).toNat)
    (hd : env s₀.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s₀.mem b) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s₀.mem b (5696 + 128 * i) = powerPoint p (start + i)) :
    WP isa (.loop accumulateBody .ne) s₀ fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = after scalar p start ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      LoopKeep b s₀ t := by
  apply WP.loop (AccumulateInv s₀ b start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := h.bound; omega
    refine WP.mono (accumulateBody_ok h.ctx h.lim k start scalar p hk h.counter
      (h.bits k hk) h.d (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
      fun t ⟨tc, tz, tl, tv, td, tk⟩ => ?_
    have hb' : ∀ i < 16, t.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
        BitVec.ofNat 8 (scalarBit scalar (start + i)).toNat :=
      fun i hi => (tk.bit i hi).trans (h.bits i hi)
    have ht' : ∀ i < 16, tablePoint t.mem b (5696 + 128 * i) = powerPoint p (start + i) := by
      intro i hi
      exact (workspace_tablePoint tk.frame (by omega) (by omega)).trans (h.table i hi)
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, tz, decide_true, Bool.not_true], tl, tv, td, h.keep.trans tk⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, tz, decide_eq_false hk0, Bool.not_false],
        k, by omega, ⟨by omega, by omega, tk.ctx h.ctx, tl, tc, td, tv, hb', ht', h.keep.trans tk⟩⟩
  · exact ⟨by decide, by decide, hc, hl, h11, hd, hp, hb, ht, LoopKeep.refl _ _⟩

theorem accumulate16_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (start scalar : Nat) (p : Spec.Ed25519.Point)
    (hb : ∀ i < 16, s.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
      BitVec.ofNat 8 (scalarBit scalar (start + i)).toNat)
    (hd : env s.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s.mem b) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s.mem b (5696 + 128 * i) = powerPoint p (start + i)) :
    WP isa accumulate16 s fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = after scalar p start ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      LoopKeep b s t := by
  refine WP.seq (wp_movw fun u hu => WP.block_nil ?_)
  have ku : LoopKeep b s u := LoopKeep.of_rest (hu.rest (ws := [.r11]) (by decide)) (by decide) hu.mem
  refine WP.mono (accumulateLoop_ok (ku.ctx hc) (by rw [hu.mem]; exact hl) start scalar p hu.gpr
    (by rw [hu.mem]; exact hb) (by rw [hu.mem]; exact hd) (by rw [hu.mem]; exact hp)
    (by rw [hu.mem]; exact ht)) fun t ⟨tl, tv, td, tk⟩ => ?_
  exact ⟨tl, tv, td, ku.trans tk⟩

end VG.Proof.Ed25519.Arm
