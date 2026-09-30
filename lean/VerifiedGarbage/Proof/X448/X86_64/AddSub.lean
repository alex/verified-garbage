import VerifiedGarbage.Proof.X448.X86_64.Columns
import VerifiedGarbage.Proof.X448.Difference

/-!
# X448 on x86-64: addition and subtraction

Untrusted: everything here is checked by Lean. Subtraction adds twice the
prime limbwise before subtracting, so every intermediate remains nonnegative.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

theorem addStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (hb : Slot b) (hi : i < 16) :
    WP isa (.block [.mov .rax (.mem (sc (a + 8 * i))),
      .alu .add .rax (.mem (sc (b + 8 * i))), .store (sc (TMP + 8 * i)) .rax]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 8 * i))
        (BitVec.ofNat 64 (limbs s.mem base a i + limbs s.mem base b i)) ∧ Keeps clob s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have w := hs.write (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, ea_sc,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, hs.rdi, la, lb, w, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [limbs, limbs, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]
  · have hr' : r ≠ .rax := fun h => hr (by subst r; decide)
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr', ite_false]

theorem subK_nat (i : Nat) : (BitVec.signExtend 64 (subK i)).toNat = bias i := by
  by_cases h : i = 8 <;> simp only [subK, bias, h, ite_true, ite_false] <;> decide

theorem subStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : Slot a) (hb : Slot b) (hi : i < 16)
    (ab : limbs s.mem base a i < radix) (bb : limbs s.mem base b i < radix) :
    WP isa (.block [.mov .rax (.mem (sc (a + 8 * i))), .alu .add .rax (.imm (subK i)),
      .alu .sub .rax (.mem (sc (b + 8 * i))), .store (sc (TMP + 8 * i)) .rax]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 8 * i))
        (BitVec.ofNat 64 (difference (limbs s.mem base a) (limbs s.mem base b) i)) ∧ Keeps clob s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have w := hs.write (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have biasb := bias_bound i
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, ea_sc,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, hs.rdi, la, lb, w, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (off base (TMP + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, subK_nat, BitVec.toNat_ofNat, difference]
    change (2 ^ 64 - limbs s.mem base b i + (limbs s.mem base a i + bias i) % 2 ^ 64) % 2 ^ 64 =
      (limbs s.mem base a i + bias i - limbs s.mem base b i) % 2 ^ 64
    have hr : radix = 268435456 := rfl
    omega
  · have hr' : r ≠ .rax := fun h => hr (by subst r; decide)
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr', ite_false]

theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.X448.X86_64.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i < _
    simp only [radix] at h1 h2
    omega
  refine WP.mono (columns_normalize hs ho fb (columns_ok hs (by decide : .rdi ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_add ?_⟩
  · intro i hi t ts tm _
    refine WP.mono (addStep_ok ts ha hb hi) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    rw [input_limb tm ha hi, input_limb tm hb hi] at um
    exact um
  · rw [tv, valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block (Impl.X448.X86_64.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  let f := difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : ∀ i < 16, f i < 2 ^ 62 := difference_bound ab
  refine WP.mono (columns_normalize hs ho fb (columns_ok hs (by decide : .rdi ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_sub ?_⟩
  · intro i hi t ts tm _
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subStep_ok ts ha hb hi (ea ▸ ab i hi) (eb ▸ bb i hi)) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    simp only [difference, ea, eb] at um
    exact um
  · rw [Nat.add_mod, tv, ← Nat.add_mod, difference_val bb, Nat.add_mul_mod_self_right]

end VG.Proof.X448.X86_64
