import VerifiedGarbage.Proof.X448.Arm.Columns

/-!
# X448 on ARMv7: addition and subtraction

Untrusted: everything here is checked by Lean. Twice the prime is added
before subtraction, so no limb subtraction borrows.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_dp wp_movw op2_reg op2_imm)

theorem addStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (hb : Slot b) (hi : i < 28) :
    WP isa (.block [ld .r3 (a + 4 * i), ld .r2 (b + 4 * i),
      .dp .add .r3 .r3 (.reg .r2), st .r3 (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i))
        (BitVec.ofNat 32 (limbs s.mem base a i + limbs s.mem base b i)) ∧ Keeps clob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide) (by decide)
  refine load_ok ts (by omega) fun u hu => ?_
  have us := ts.of_upd hu (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun v hv => ?_
  have vs := us.of_upd hv (by decide) (by decide)
  refine store_ok vs (by simp only [TMP]; omega) fun w hw => WP.block_nil ⟨?_, ?_⟩
  · rw [hw.mem, hv.mem, hu.mem, ht.mem, hv.gpr]
    change s.mem.writeW _ (u.gpr .r3 + u.gpr .r2) = _
    rw [hu.other .r3 (by decide), ht.gpr, hu.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans (hw.rest _))))

theorem subK_nat (i : Nat) : ((subK i).setWidth 32 + (65536 : BitVec 32)).toNat = bias i := by
  by_cases h : i = 14 <;> simp only [subK, bias, h, ite_true, ite_false] <;> decide

theorem subStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (hb : Slot b) (hi : i < 28)
    (ab : limbs s.mem base a i < radix) (bb : limbs s.mem base b i < radix) :
    WP isa (.block [ld .r3 (a + 4 * i), .movw .r2 (subK i), .dp .add .r2 .r2 (.imm 65536),
      .dp .add .r3 .r3 (.reg .r2), ld .r2 (b + 4 * i), .dp .sub .r3 .r3 (.reg .r2),
      st .r3 (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i))
        (BitVec.ofNat 32 (difference (limbs s.mem base a) (limbs s.mem base b) i)) ∧ Keeps clob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine load_ok hs (by omega) fun s1 h1 => ?_
  have hs1 := hs.of_upd h1 (by decide) (by decide)
  refine wp_movw fun s2 h2 => ?_
  have hs2 := hs1.of_upd h2 (by decide) (by decide)
  refine wp_dp (op2_imm (by decide)) fun s3 h3 => ?_
  have hs3 := hs2.of_upd h3 (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s4 h4 => ?_
  have hs4 := hs3.of_upd h4 (by decide) (by decide)
  refine load_ok hs4 (by omega) fun s5 h5 => ?_
  have hs5 := hs4.of_upd h5 (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s6 h6 => ?_
  have hs6 := hs5.of_upd h6 (by decide) (by decide)
  refine store_ok hs6 (by simp only [TMP]; omega) fun s7 h7 => WP.block_nil ⟨?_, ?_⟩
  · rw [h7.mem, h6.mem, h5.mem, h4.mem, h3.mem, h2.mem, h1.mem, h6.gpr]
    change s.mem.writeW _ (s5.gpr .r3 - s5.gpr .r2) = _
    rw [h5.other .r3 (by decide), h4.gpr, h5.gpr, h4.mem, h3.mem, h2.mem, h1.mem]
    change s.mem.writeW _ (s3.gpr .r3 + s3.gpr .r2 - word s.mem base (b + 4 * i)) = _
    rw [h3.other .r3 (by decide), h2.other .r3 (by decide), h1.gpr, h3.gpr]
    change s.mem.writeW _ (word s.mem base (a + 4 * i) + (s2.gpr .r2 + 65536) - _) = _
    rw [h2.gpr]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, subK_nat, BitVec.toNat_ofNat]
    change (2 ^ 32 - limbs s.mem base b i + (limbs s.mem base a i + bias i) % 2 ^ 32) % 2 ^ 32 =
      (limbs s.mem base a i + bias i - limbs s.mem base b i) % 2 ^ 32
    have h := bias_bound i
    simp only [radix] at ab bb h
    omega
  · exact rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans
      ((h3.rest (by decide)).trans ((h4.rest (by decide)).trans ((h5.rest (by decide)).trans
      ((h6.rest (by decide)).trans (h7.rest _)))))))

theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.X448.Arm.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i ≤ _
    simp only [radix] at h1 h2 ⊢
    omega
  refine WP.mono (columns_normalize hs ho fb (columns_ok hs (by decide : .r0 ∉ clob ∧ .r6 ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_add ?_⟩
  · intro i hi t ts tm _
    refine WP.mono (addStep_ok ts ha hb hi) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    rw [input_limb tm ha hi, input_limb tm hb hi] at um
    exact um
  · rw [tv, valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.X448.Arm.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  let f := difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := fun i hi => Nat.le_of_lt (difference_bound ab i hi)
  refine WP.mono (columns_normalize hs ho fb (columns_ok hs (by decide : .r0 ∉ clob ∧ .r6 ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_sub ?_⟩
  · intro i hi t ts tm _
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subStep_ok ts ha hb hi (ea ▸ ab i hi) (eb ▸ bb i hi)) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    simp only [difference, ea, eb] at um
    exact um
  · rw [Nat.add_mod, tv, ← Nat.add_mod, difference_val bb, Nat.add_mul_mod_self_right]

end VG.Proof.X448.Arm
