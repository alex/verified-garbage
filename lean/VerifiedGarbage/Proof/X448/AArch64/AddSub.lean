import VerifiedGarbage.Proof.X448.AArch64.Columns
import VerifiedGarbage.Proof.X448.Difference

/-!
# X448 on AArch64: addition and subtraction

Untrusted: everything here is checked by Lean. Subtraction adds twice the
prime limbwise before subtracting, so every intermediate remains nonnegative.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem addStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (hi : i < 16) :
    WP isa (.block [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 .x5, st .x4 (TMP + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 8 * i))
        (BitVec.ofNat 64 (limbs s.mem base a i + limbs s.mem base b i)) ∧ Keeps clob s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have w := hs.write (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  have oe : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 32768 := by simp only [TMP]; omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, oe, and_self,
    hs.x3, la, lb, w, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (off base (TMP + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  · have hr' : r ≠ .x4 := fun h => hr (by subst r; decide)
    have hr'' : r ≠ .x5 := fun h => hr (by subst r; decide)
    simp only [RegUpd.gpr_write, hr', hr'', ite_false]

theorem subK_nat (i : Nat) : ((subK i).setWidth 64 &&& ~~~((65535 : BitVec 64) <<< (16 : Nat)) ||| (8191 : BitVec 16).setWidth 64 <<< (16 : Nat)).toNat = bias i := by
  by_cases h : i = 8 <;> simp only [subK, bias, h, ite_true, ite_false] <;> decide

theorem subStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (hi : i < 16)
    (ab : limbs s.mem base a i < radix) (bb : limbs s.mem base b i < radix) :
    WP isa (.block [ld .x4 (a + 8 * i), .movz .x .x5 (subK i) 0, .movk .x .x5 0x1fff 1,
      .add .x .x4 .x4 .x5, ld .x5 (b + 8 * i), .sub .x .x4 .x4 .x5, st .x4 (TMP + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 8 * i))
        (BitVec.ofNat 64 (difference (limbs s.mem base a) (limbs s.mem base b) i)) ∧ Keeps clob s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have w := hs.write (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have biasb := bias_bound i
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  have oe : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 32768 := by simp only [TMP]; omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, oe, and_self,
    hs.x3, la, lb, w, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (off base (TMP + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, subK_nat, BitVec.toNat_ofNat, difference]
    change (2 ^ 64 - limbs s.mem base b i + (limbs s.mem base a i + bias i) % 2 ^ 64) % 2 ^ 64 =
      (limbs s.mem base a i + bias i - limbs s.mem base b i) % 2 ^ 64
    have hr : radix = 268435456 := rfl
    omega
  · have hr' : r ≠ .x4 := fun h => hr (by subst r; decide)
    have hr'' : r ≠ .x5 := fun h => hr (by subst r; decide)
    simp only [RegUpd.gpr_write, hr', hr'', ite_false]

theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.X448.AArch64.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i < _
    simp only [radix] at h1 h2
    omega
  refine WP.mono (columns_normalize hs ho ho8 fb (columns_ok hs (by decide : .x3 ∉ clob ∧ .x12 ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_add ?_⟩
  · intro i hi t ts tm _
    refine WP.mono (addStep_ok ts ha ha8 hb hb8 hi) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    rw [input_limb tm ha hi, input_limb tm hb hi] at um
    exact um
  · rw [tv, valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0) (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.X448.AArch64.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  let f := difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : ∀ i < 16, f i < 2 ^ 62 := difference_bound ab
  refine WP.mono (columns_normalize hs ho ho8 fb (columns_ok hs (by decide : .x3 ∉ clob ∧ .x12 ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_sub ?_⟩
  · intro i hi t ts tm _
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subStep_ok ts ha ha8 hb hb8 hi (ea ▸ ab i hi) (eb ▸ bb i hi)) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    simp only [difference, ea, eb] at um
    exact um
  · rw [Nat.add_mod, tv, ← Nat.add_mod, difference_val bb, Nat.add_mul_mod_self_right]

end VG.Proof.X448.AArch64
