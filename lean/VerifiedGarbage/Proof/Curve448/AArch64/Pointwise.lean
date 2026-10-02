import VerifiedGarbage.Proof.Curve448.AArch64.AddEval
import VerifiedGarbage.Proof.Curve448.AArch64.SubEval
import VerifiedGarbage.Proof.Curve448.AArch64.SmallEval
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Proof.X448.AArch64

theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.Curve448.AArch64.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : Within (radix * 6) f := by
    intro i hi; have h1 := ab i hi; have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i < _
    simp only [weakBound, radix] at h1 h2 ⊢; omega
  refine WP.mono (stage_point hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_add ?_⟩
  · intro i hi t ts tm
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (addEval_ok ts ha ha8 hb hb8 hi (ea ▸ ab i hi) (eb ▸ bb i hi))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    rw [ea, eb] at uv; exact uv
  · rw [tv, valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.Curve448.AArch64.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  let f := difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : Within (radix * 6) f := by
    intro i hi; have h := ab i hi
    change difference (limbs s.mem base a) (limbs s.mem base b) i < _
    simp only [difference, bias, weakBound, radix] at h ⊢
    split <;> omega
  refine WP.mono (stage_point hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_sub ?_⟩
  · intro i hi t ts tm
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subEval_ok ts ha ha8 hb hb8 hi (ea ▸ ab i hi) (eb ▸ bb i hi))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    simp only [difference, ea, eb] at uv; exact uv
  · rw [Nat.add_mod, tv, ← Nat.add_mod, difference_val bb,
      Nat.mul_comm 4 Spec.X448.P, Nat.add_mul_mod_self_left]

theorem small_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (ab : Bounded s.mem base a) :
    WP isa (.block (Impl.Curve448.AArch64.small o a)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : Within (2 ^ 118) f := by
    intro i hi
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))) (by decide)
  refine WP.mono (stage_normalize hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_a24 ?_⟩
  · intro i hi t ts tm
    refine WP.mono (smallEval_ok ts ha ha8 hi) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono (by decide)⟩
    rw [input_limb tm ha hi] at uv; exact uv
  · rw [tv, valN_scale]
end VG.Proof.Curve448.AArch64
