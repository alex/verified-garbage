import VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep

/-! Consume one sixteen-bit batch from most significant bit to least. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure AccumulateInv (x : BitVec 32) (s₀ : State) (scalar batch : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  keep : IKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = after scalar p (16 * batch + n)
  d : env s.mem x 16 = Spec.Ed25519.d

theorem accumulateLoop_ok {x : BitVec 32} {s₀ : State} (hc : Ctx x s₀)
    (scalar batch : Nat) (p : Spec.Ed25519.Point) (hb : batch < 32)
    (hindex : wd s₀.mem x 28 = BitVec.ofNat 32 batch)
    (hcounter : s₀.gpr .esi = BitVec.ofNat 32 16)
    (hbits : ∀ j < 16, s₀.mem (addr x (7168 + (16 * batch + j))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * batch + j)).toNat)
    (htable : ∀ j < 16, tablePoint s₀.mem x (5120 + 128 * j) = powerPoint p (16 * batch + j))
    (hp : point (env s₀.mem x) 0 1 2 3 = after scalar p (16 * batch + 16))
    (hd : env s₀.mem x 16 = Spec.Ed25519.d) :
    WP isa (.loop (.block accumulateBody) .ne) s₀ fun t => IKeep x s₀ t ∧
      point (env t.mem x) 0 1 2 3 = after scalar p (16 * batch) ∧ env t.mem x 16 = Spec.Ed25519.d := by
  apply WP.loop (fun n => AccumulateInv x s₀ scalar batch p n) (n := 16)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < 16 := by have := h.bound; omega
    refine WP.mono (accumulateBody_ok (h.keep.ctx hc) j batch scalar p hj hb
      ((h.keep.word hc 28 (by decide)).trans hindex) h.counter
      ((h.keep.bit hc _ (by omega)).trans (hbits j hj)) h.d
      (by simpa only [Nat.add_assoc] using h.value)
      ((workspace_table h.keep hc _ (by omega) (by omega)).trans (htable j hj)))
      fun t ⟨kt, bt, zt, pt, dt⟩ => ?_
    have keep := h.keep.trans kt
    by_cases hz : j = 0
    · subst j
      exact .inl ⟨by rw [zt]; rfl, keep, by simpa only [Nat.add_zero] using pt, dt⟩
    · exact .inr ⟨by rw [zt]; simp only [decide_eq_false hz]; rfl,
        j, by omega, ⟨by omega, by omega, keep, bt, pt, dt⟩⟩
  · exact ⟨by decide, by decide, IKeep.refl _ _, hcounter, hp, hd⟩

theorem accumulate16_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (scalar batch : Nat) (p : Spec.Ed25519.Point) (hb : batch < 32)
    (hindex : wd s.mem x 28 = BitVec.ofNat 32 batch)
    (hbits : ∀ j < 16, s.mem (addr x (7168 + (16 * batch + j))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * batch + j)).toNat)
    (htable : ∀ j < 16, tablePoint s.mem x (5120 + 128 * j) = powerPoint p (16 * batch + j))
    (hp : point (env s.mem x) 0 1 2 3 = after scalar p (16 * batch + 16))
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa accumulate16 s fun t => IKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = after scalar p (16 * batch) ∧ env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (Wp.wp_movi fun u hu => WP.block_nil ?_)
  have ku : IKeep x s u := IKeep.of_counter hu
  refine WP.mono (accumulateLoop_ok (ku.ctx hc) scalar batch p hb
    (by rw [hu.mem]; exact hindex) hu.gpr (by rw [hu.mem]; exact hbits)
    (by rw [hu.mem]; exact htable) (by rw [hu.mem]; exact hp) (by rw [hu.mem]; exact hd))
    fun t ⟨kt, pt, dt⟩ => ?_
  exact ⟨ku.trans kt, pt, dt⟩

end VG.Proof.Ed25519.X86
