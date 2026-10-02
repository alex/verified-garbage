import VerifiedGarbage.Proof.X448.AArch64.PointwiseFused
import VerifiedGarbage.Proof.X448.AArch64.PointwiseAdd
import VerifiedGarbage.Proof.X448.AArch64.PointwiseSub
import VerifiedGarbage.Proof.X448.AArch64.PointwiseSmall

/-! Untrusted: fused pointwise operations satisfy the existing slot contract. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem pointwiseAdd_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Pointwise.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i < _
    simp only [radix] at h1 h2
    omega
  refine WP.mono (pointwiseFused_ok hs ho ho8 fb ?_)
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_add ?_⟩
  · intro i hi t ts tm
    refine WP.mono (addEval_ok ts ha ha8 hb hb8 hi) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk⟩
    rw [input_limb tm ha hi, input_limb tm hb hi] at uv
    exact uv
  · rw [tv, valN_add]

theorem pointwiseSub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Pointwise.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  let f := difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : ∀ i < 16, f i < 2 ^ 62 := difference_bound ab
  refine WP.mono (pointwiseFused_ok hs ho ho8 fb ?_)
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_sub ?_⟩
  · intro i hi t ts tm
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subEval_ok ts ha ha8 hb hb8 hi (ea ▸ ab i hi) (eb ▸ bb i hi)) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk⟩
    simp only [difference, ea, eb] at uv
    exact uv
  · rw [Nat.add_mod, tv, ← Nat.add_mod, difference_val bb, Nat.add_mul_mod_self_right]

theorem pointwiseSmall_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0) (ab : Bounded s.mem base a) :
    WP isa (.block (Pointwise.small o a)) s fun t => Op base o s t ∧ Bounded t.mem base o ∧
      F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * radix < 2 ^ 62 := by decide
    exact Nat.lt_of_le_of_lt h hr
  refine WP.mono (pointwiseFused_ok hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_a24 ?_⟩
  · intro i hi t ts tm
    refine WP.mono (smallEval_ok ts ha ha8 hi) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk⟩
    rw [input_limb tm ha hi] at uv
    exact uv
  · rw [tv, valN_scale]

end VG.Proof.X448.AArch64
