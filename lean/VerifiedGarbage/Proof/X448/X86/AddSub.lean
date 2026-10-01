import VerifiedGarbage.Proof.X448.X86.Columns

/-!
# X448 on x86 (32-bit): addition and subtraction

Untrusted: everything here is checked by Lean. Twice the prime is added
before subtraction, so no limb subtraction borrows.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem addStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (hb : Slot b) (hi : i < 28) :
    WP isa (.block [ld .eax (a + 4 * i), .alu .add .eax (.mem (sc (b + 4 * i))),
      st .eax (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i))
        (BitVec.ofNat 32 (limbs s.mem base a i + limbs s.mem base b i)) ∧ Keeps clob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  have rd : readSrc t (.mem (sc (b + 4 * i))) = some (word t.mem base (b + 4 * i)) := by
    simp only [readSrc, ts.ea (d := b + 4 * i) (by omega), State.load32, ts.read (d := b + 4 * i) (n := 4) (by omega), ite_true]
  refine wp_alu (Or.inl rfl) rd fun u hu _ => ?_
  refine store_ok (ts.of_upd hu (by decide)) (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]
    change s.mem.writeW _ (t.gpr .eax + word t.mem base (b + 4 * i)) = _
    rw [ht.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  · exact (ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _))

theorem subK_nat (i : Nat) : (subK i).toNat = bias i := by
  by_cases h : i = 14 <;> simp only [subK, bias, h, ite_true, ite_false] <;> decide

theorem subStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (hb : Slot b) (hi : i < 28)
    (ab : limbs s.mem base a i < radix) (bb : limbs s.mem base b i < radix) :
    WP isa (.block [ld .eax (a + 4 * i), .alu .add .eax (.imm (subK i)),
      .alu .sub .eax (.mem (sc (b + 4 * i))), st .eax (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i))
        (BitVec.ofNat 32 (difference (limbs s.mem base a) (limbs s.mem base b) i)) ∧ Keeps clob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine load_ok hs (by omega) fun t ht => ?_
  refine wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  have us := (hs.of_upd ht (by decide)).of_upd hu (by decide)
  have rd : readSrc u (.mem (sc (b + 4 * i))) = some (word u.mem base (b + 4 * i)) := by
    simp only [readSrc, us.ea (d := b + 4 * i) (by omega), State.load32, us.read (d := b + 4 * i) (n := 4) (by omega), ite_true]
  refine wp_alu (Or.inr (Or.inl rfl)) rd fun v hv _ => ?_
  refine store_ok (us.of_upd hv (by decide)) (by simp only [TMP]; omega) fun w hw => WP.block_nil ⟨?_, ?_⟩
  · rw [hw.mem, hv.mem, hu.mem, ht.mem, hv.gpr]
    change s.mem.writeW _ (u.gpr .eax - word u.mem base (b + 4 * i)) = _
    rw [hu.gpr, hu.mem, ht.mem]
    change s.mem.writeW _ (t.gpr .eax + subK i - _) = _
    rw [ht.gpr]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, subK_nat, BitVec.toNat_ofNat]
    change (2 ^ 32 - limbs s.mem base b i + (limbs s.mem base a i + bias i) % 2 ^ 32) % 2 ^ 32 =
      (limbs s.mem base a i + bias i - limbs s.mem base b i) % 2 ^ 32
    have h := bias_bound i
    simp only [radix] at ab bb h
    omega
  · exact (ht.rest (by decide)).trans ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest _)))

theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.X448.X86.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i ≤ _
    simp only [radix] at h1 h2 ⊢
    omega
  refine WP.mono (columns_normalize hs ho fb (columns_ok hs (by decide : .edi ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_add ?_⟩
  · intro i hi t ts tm _
    refine WP.mono (addStep_ok ts ha hb hi) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    rw [input_limb tm ha hi, input_limb tm hb hi] at um
    exact um
  · rw [tv, valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.X448.X86.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  let f := difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := fun i hi => Nat.le_of_lt (difference_bound ab i hi)
  refine WP.mono (columns_normalize hs ho fb (columns_ok hs (by decide : .edi ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_sub ?_⟩
  · intro i hi t ts tm _
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subStep_ok ts ha hb hi (ea ▸ ab i hi) (eb ▸ bb i hi)) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    simp only [difference, ea, eb] at um
    exact um
  · rw [Nat.add_mod, tv, ← Nat.add_mod, difference_val bb, Nat.add_mul_mod_self_right]

end VG.Proof.X448.X86
