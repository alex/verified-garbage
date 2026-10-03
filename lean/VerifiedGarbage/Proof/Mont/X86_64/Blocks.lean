import VerifiedGarbage.Proof.Mont.X86_64.Row
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# Montgomery arithmetic on x86-64: the small blocks of a round

Each run symbolically once, for any registers: loading a word into `rcx`,
a row with its carry word cleared first (`mulRow`), the carry of a row into
the two top words (`carryUp`), and the computation of `u = t₀ m' mod 2⁶⁴`.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry toNat_ofBool)

theorem movRcx_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rcx (.mem (sc d))]) s fun s' =>
      s'.gpr .rcx = word s.mem base d ∧ Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs hd, Option.map_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- A row, with the carry word cleared first. -/
theorem mulRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {ts : List Reg}
    {d : Nat} (hd : d + 8 * ts.length ≤ size) (hf : Fresh ts) :
    WP isa (.block (mulRow ts d)) s fun s' =>
      regsVal s' ts + 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat =
        regsVal s ts + (s.gpr .rcx).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.rbp :: .rax :: .rdx :: ts) s s' := by
  rw [mulRow, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rbp (.imm 0)]) s
      (fun s₁ => s₁.gpr .rbp = 0 ∧ Keeps [.rbp] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨b₁, k₁⟩ => ?_
  refine WP.mono (mulSteps_ok ts (hs.of_keeps k₁ (by decide)) hd hf) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (hf.2 q hq).2.2.2.1)
  rw [b₁, hR, k₁.2.1, k₁.1 .rcx (by decide)] at e₂
  refine ⟨by simpa using e₂, (k₁.mono (by sub_regs)).trans k₂⟩

/-- The carry word `rbp` into `tn` and its carry into `tn1`, if that does not
overflow. -/
theorem carryUp_ok (s : State) {tn tn1 : Reg} (h1 : tn ≠ tn1)
    (hb : (s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat + (s.gpr .rbp).toNat < 2 ^ 128) :
    WP isa (.block (carryUp tn tn1)) s fun s' =>
      (s'.gpr tn).toNat + 2 ^ 64 * (s'.gpr tn1).toNat =
        (s.gpr tn).toNat + 2 ^ 64 * (s.gpr tn1).toNat + (s.gpr .rbp).toNat ∧
      Keeps [tn, tn1] s s' := by
  apply WP.of_runBlock
  simp only [carryUp, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, h1, Ne.symm h1,
    Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e0 := add_carry (s.gpr tn) (s.gpr .rbp)
    have e1 := adc_carry (s.gpr tn1) 0 (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .rbp).toNat))
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz, Nat.add_zero] at e1
    have := (s.gpr tn1 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ (s.gpr tn).toNat +
      (s.gpr .rbp).toNat))).setWidth 64).isLt
    have := Bool.toNat_le (decide (2 ^ 64 ≤ (s.gpr tn1).toNat +
      (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .rbp).toNat)).toNat))
    have hc : (decide (2 ^ 64 ≤ (s.gpr tn1).toNat +
      (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .rbp).toNat)).toNat)).toNat = 0 := by
      have := Bool.toNat_le (decide (2 ^ 64 ≤ (s.gpr tn).toNat + (s.gpr .rbp).toNat))
      omega
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- `rcx = t₀ m' mod 2⁶⁴`. -/
theorem uBlock_ok (s : State) (t0 : Reg) (minv : BitVec 64) :
    WP isa (.block [.mov .rax (.reg t0), .movImm64 .rcx minv, .mul .rcx, .mov .rcx (.reg .rax)]) s
      fun s' => (s'.gpr .rcx).toNat = (s.gpr t0).toNat * minv.toNat % 2 ^ 64 ∧
        Keeps [.rax, .rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  refine ⟨BitVec.toNat_ofNat _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Mont.X86_64
