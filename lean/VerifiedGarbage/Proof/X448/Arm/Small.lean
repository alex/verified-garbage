import VerifiedGarbage.Proof.X448.Arm.Columns

/-!
# X448 on ARMv7: multiplication by a24

The 16-bit limbs keep multiplication by 39081 within a 32-bit word.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_mul wp_movw)

theorem smallStep_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : Slot a) (hi : i < 28) (hc : (s.gpr .r5).toNat = 39081) :
    WP isa (.block [ld .r3 (a + 4 * i), .mul .r3 .r3 .r5, st .r3 (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (39081 * limbs s.mem base a i)) ∧
      Keeps [.r3, .r2] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  refine load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide) (by decide)
  refine wp_mul fun u hu => ?_
  have us := ts.of_upd hu (by decide) (by decide)
  refine store_ok us (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr, ht.gpr, ht.other .r5 (by decide)]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, hc, Nat.mul_comm _ 39081, BitVec.toNat_ofNat]
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

theorem smallInit_ok (s : State) :
    WP isa (.block [.movw .r5 39081]) s fun t =>
      (t.gpr .r5).toNat = 39081 ∧ t.mem = s.mem ∧ Keeps [.r5] s t := by
  refine wp_movw fun t ht => WP.block_nil ⟨?_, ht.mem, rest_keeps (ht.rest (by decide))⟩
  rw [ht.gpr]
  rfl

theorem mulSmall_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa (.block (mulSmall o a)) s fun t => Op base o s t ∧ Bounded t.mem base o ∧
      F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * radix ≤ 2 ^ 32 - radix := by decide
    exact Nat.le_trans h hr
  refine WP.mono (columns_normalize hs ho fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_a24 ?_⟩
  · rw [WP.block_append_iff]
    refine WP.mono (smallInit_ok s) fun t ⟨tc, tm, tk⟩ => ?_
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (columns_ok ts (by decide : Reg.r0 ∉ [Reg.r3, Reg.r2] ∧ Reg.r6 ∉ [Reg.r3, Reg.r2]) fb ?_) fun u ⟨uf, um, uk⟩ => ?_
    · intro i hi u us um uk
      have uc : (u.gpr .r5).toNat = 39081 := by rw [uk.1 _ (by decide), tc]
      refine WP.mono (smallStep_ok us ha hi uc) fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
      rw [input_limb um ha hi, tm] at vm
      exact vm
    · refine ⟨uf, ?_, (tk.mono ?_).trans (uk.mono ?_)⟩
      · rw [← tm]; exact um
      · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
  · rw [tv, valN_scale]

end VG.Proof.X448.Arm
