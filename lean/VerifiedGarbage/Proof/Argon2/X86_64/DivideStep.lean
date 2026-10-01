import VerifiedGarbage.Impl.Argon2.X86_64.Divide
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! # One bit of Argon2's fixed-time index division -/

namespace VG.Proof.Argon2.X86_64.Divide

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Divide

/-- All state except the listed registers and arithmetic flags is unchanged. -/
structure Keeps (rs : List Reg) (s t : State) : Prop where
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem Keeps.mono {rs rs' : List Reg} {s t : State} (h : Keeps rs s t)
    (hh : ∀ r ∈ rs, r ∈ rs') : Keeps rs' s t :=
  ⟨fun r hr => h.regs r (fun hm => hr (hh r hm)), h.mem, h.rd, h.wr, h.mxcsr⟩

theorem Keeps.trans {rs : List Reg} {s t u : State} (h : Keeps rs s t)
    (k : Keeps rs t u) : Keeps rs s u :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.mem.trans h.mem,
    k.rd.trans h.rd, k.wr.trans h.wr, k.mxcsr.trans h.mxcsr⟩

def mask (b : Bool) : BitVec 64 := if b then -1 else 0

theorem sbb_mask (x : BitVec 64) (b : Bool) :
    x - x - (BitVec.ofBool b).setWidth 64 = mask b := by
  rw [BitVec.sub_self]
  cases b <;> decide

theorem subtract_ok (s : State) (j : Nat) (hj : j < 32) :
    let v := s.gpr .r8 + s.gpr .r8 +
      (BitVec.ofBool ((s.gpr .rdi).getLsbD j)).setWidth 64
    WP isa (.block (subtract j)) s fun t =>
      t.gpr .r8 = v - s.gpr .rsi ∧ t.gpr .r10 = v ∧
      t.gpr .rax = mask (decide (v.toNat < (s.gpr .rsi).toNat)) ∧
      Keeps [.rcx, .r8, .r10, .rax] s t := by
  intro v
  apply WP.of_runBlock
  simp only [subtract, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags,
    RegUpd.cf_arithFlags, show 1 ≤ j + 1 ∧ j + 1 ≤ 63 by omega,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', Nat.add_sub_cancel, and_self, sbb_mask]
  refine ⟨rfl, rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
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

theorem select_ok (s : State) (b : Bool) (hm : s.gpr .rax = mask b) :
    WP isa (.block select) s fun t =>
      t.gpr .r8 = (if b then s.gpr .r10 else s.gpr .r8) ∧
      t.gpr .r9 = (s.gpr .r9 + s.gpr .r9) + (if b then 0 else 1) ∧
      Keeps [.r10, .r8, .rax, .r9] s t := by
  apply WP.of_runBlock
  simp only [select, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.bind_some,
    Option.some.injEq, exists_eq_left', hm, select_value,
    show BitVec.signExtend 64 (1 : BitVec 32) = 1 from rfl]
  refine ⟨trivial, ?_, ?_⟩
  · cases b <;> rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
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
    (hr : (s.gpr .r8).toNat < 2 ^ 32) (hq : (s.gpr .r9).toNat < 2 ^ 32) :
    let v := 2 * (s.gpr .r8).toNat + ((s.gpr .rdi).getLsbD j).toNat
    let d := (s.gpr .rsi).toNat
    WP isa (.block (bit j)) s fun t =>
      (t.gpr .r8).toNat = (if v < d then v else v - d) ∧
      (t.gpr .r9).toNat = 2 * (s.gpr .r9).toNat + (if v < d then 0 else 1) ∧
      Keeps [.rcx, .r8, .r10, .rax, .r9] s t := by
  intro v d
  rw [bit, WP.block_append_iff]
  refine (subtract_ok s j hj).mono ?_
  rintro u ⟨hu8, hu10, huax, hu⟩
  refine (select_ok u _ huax).mono ?_
  rintro t ⟨ht8, ht9, ht⟩
  have hv := double_bit (s.gpr .r8) ((s.gpr .rdi).getLsbD j) hr
  have hu9 := hu.regs .r9 (by decide)
  refine ⟨?_, ?_, (hu.mono (by decide)).trans (ht.mono (by decide))⟩
  · simp only [ht8, hu8, hu10, decide_eq_true_eq]
    rw [reduced_value, hv]
  · simp only [ht9, hu9, hv, decide_eq_true_eq]
    change (s.gpr .r9 + s.gpr .r9 + (if v < d then 0 else 1)).toNat =
      2 * (s.gpr .r9).toNat + (if v < d then 0 else 1)
    by_cases h : v < d
    · simp only [h, ite_true]
      exact double_bit (s.gpr .r9) false hq
    · simp only [h, ite_false]
      exact double_bit (s.gpr .r9) true hq

end VG.Proof.Argon2.X86_64.Divide
