import VerifiedGarbage.Impl.Argon2.AArch64.Divide
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Argon2.AArch64.Carry

/-! # One bit of Argon2's fixed-time index division -/

namespace VG.Proof.Argon2.AArch64.Divide

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Divide

/-- All state except the listed registers and arithmetic flags is unchanged. -/
structure Keeps (rs : List Reg) (s t : State) : Prop where
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keeps.mono {rs rs' : List Reg} {s t : State} (h : Keeps rs s t)
    (hh : ∀ r ∈ rs, r ∈ rs') : Keeps rs' s t :=
  ⟨fun r hr => h.regs r (fun hm => hr (hh r hm)), h.mem, h.rd, h.wr, h.sp⟩

theorem Keeps.trans {rs : List Reg} {s t u : State} (h : Keeps rs s t)
    (k : Keeps rs t u) : Keeps rs s u :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.mem.trans h.mem,
    k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

def mask (b : Bool) : BitVec 64 := if b then -1 else 0

theorem difference_high (a b : BitVec 64) (ha : a.toNat < 2 ^ 63)
    (hb : b.toNat < 2 ^ 63) :
    (a - b) >>> (63 : Nat) = if a.toNat < b.toNat then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  by_cases h : a.toNat < b.toNat
  · rw [ite_eq_left h, BitVec.toNat_sub_of_lt (by rw [BitVec.lt_def]; exact h)]
    simp only [show (1 : BitVec 64).toNat = 1 from rfl, Nat.reducePow] at *
    omega
  · rw [ite_eq_right h, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_of_not_gt h)]
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.reducePow] at *
    omega

theorem subtract_ok (s : State) (j : Nat) (hj : j < 32)
    (ha : (s.gpr .x4).toNat < 2 ^ 32) (hb : (s.gpr .x1).toNat < 2 ^ 32) :
    let v := s.gpr .x4 + s.gpr .x4 +
      (BitVec.ofBool ((s.gpr .x0).getLsbD j)).setWidth 64
    WP isa (.block (subtract j)) s fun t =>
      t.gpr .x4 = v - s.gpr .x1 ∧ t.gpr .x6 = v ∧
      t.gpr .x8 = mask (decide (v.toNat < (s.gpr .x1).toNat)) ∧
      Keeps [.x3, .x4, .x6, .x8, .x9] s t := by
  intro v
  apply WP.of_runBlock
  simp only [subtract, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, RegUpd.gpr_write, Size.bits, show j < 64 by omega,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, show 0 < 4096 from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_eq, BitVec.and_one_eq_setWidth_ofBool_getLsbD,
    BitVec.getLsbD_ushiftRight, show 63 < 64 from by decide,
    show ((1 : BitVec 16).setWidth 64) = 1#64 from rfl,
    show ((0 : BitVec 16).setWidth 64) = 0#64 from rfl, BitVec.add_zero]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · have hv : v.toNat < 2 ^ 63 := by
      have hsum : (s.gpr .x4).toNat + (s.gpr .x4).toNat < 2 ^ 64 := by omega
      have hn := Bool.toNat_le ((s.gpr .x0).getLsbD j)
      simp only [v, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
        Nat.mod_eq_of_lt hsum]
      omega
    change (0 : BitVec 64) - ((v - s.gpr .x1) >>> (63 : Nat)) = _
    rw [difference_high _ _ hv (by omega)]
    by_cases h : v.toNat < (s.gpr .x1).toNat <;>
      simp only [mask, h, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;> rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    all_goals rfl

theorem select_value (b : Bool) (reduced original : BitVec 64) :
    reduced ^^^ ((original ^^^ reduced) &&& mask b) =
      if b then original else reduced := by
  cases b
  · apply BitVec.eq_of_toNat_eq
    simp [mask]
  · simp only [mask, ite_true, show (-1 : BitVec 64) = BitVec.allOnes 64 from rfl,
      BitVec.and_allOnes]
    rw [BitVec.xor_comm original reduced, ← BitVec.xor_assoc, BitVec.xor_self,
      BitVec.zero_xor]

theorem select_ok (s : State) (b : Bool) (hm : s.gpr .x8 = mask b) :
    WP isa (.block select) s fun t =>
      t.gpr .x4 = (if b then s.gpr .x6 else s.gpr .x4) ∧
      t.gpr .x5 = (s.gpr .x5 + s.gpr .x5) + (if b then 0 else 1) ∧
      Keeps [.x6, .x4, .x8, .x5] s t := by
  apply WP.of_runBlock
  simp only [select, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, RegUpd.gpr_write,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_eq, show 1 < 4096 from by decide, hm, select_value]
  refine ⟨trivial, ?_, ?_⟩
  · cases b <;> rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    all_goals rfl

theorem double_bit (x : BitVec 64) (b : Bool) (hx : x.toNat < 2 ^ 32) :
    (x + x + (BitVec.ofBool b).setWidth 64).toNat = 2 * x.toNat + b.toNat := by
  have hsum : x.toNat + x.toNat < 2 ^ 64 := by omega
  cases b <;> simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
    Bool.toNat_false, Bool.toNat_true, Nat.zero_mod, Nat.one_mod,
    Nat.mod_eq_of_lt hsum, Nat.add_zero] <;> omega

theorem reduced_value (v d : BitVec 64) :
    (if v.toNat < d.toNat then v else v - d).toNat =
      if v.toNat < d.toNat then v.toNat else v.toNat - d.toNat := by
  split
  · rfl
  · next h =>
    rw [BitVec.toNat_sub]
    have hv := v.isLt
    have hd := d.isLt
    omega

theorem bit_ok (s : State) (j : Nat) (hj : j < 32)
    (hr : (s.gpr .x4).toNat < 2 ^ 32) (hq : (s.gpr .x5).toNat < 2 ^ 32)
    (hd : (s.gpr .x1).toNat < 2 ^ 32) :
    let v := 2 * (s.gpr .x4).toNat + ((s.gpr .x0).getLsbD j).toNat
    let d := (s.gpr .x1).toNat
    WP isa (.block (bit j)) s fun t =>
      (t.gpr .x4).toNat = (if v < d then v else v - d) ∧
      (t.gpr .x5).toNat = 2 * (s.gpr .x5).toNat + (if v < d then 0 else 1) ∧
      Keeps [.x3, .x4, .x6, .x8, .x5, .x9] s t := by
  intro v d
  rw [bit, WP.block_append_iff]
  refine (subtract_ok s j hj hr hd).mono ?_
  rintro u ⟨hu8, hu10, huax, hu⟩
  refine (select_ok u _ huax).mono ?_
  rintro t ⟨ht8, ht9, ht⟩
  have hv := double_bit (s.gpr .x4) ((s.gpr .x0).getLsbD j) hr
  have hu9 := hu.regs .x5 (by decide)
  refine ⟨?_, ?_, (hu.mono (by decide)).trans (ht.mono (by decide))⟩
  · simp only [ht8, hu8, hu10, decide_eq_true_eq]
    rw [reduced_value, hv]
  · simp only [ht9, hu9, hv, decide_eq_true_eq]
    change (s.gpr .x5 + s.gpr .x5 + (if v < d then 0 else 1)).toNat =
      2 * (s.gpr .x5).toNat + (if v < d then 0 else 1)
    by_cases h : v < d
    · simp only [h, ite_true]
      exact double_bit (s.gpr .x5) false hq
    · simp only [h, ite_false]
      exact double_bit (s.gpr .x5) true hq

end VG.Proof.Argon2.AArch64.Divide
