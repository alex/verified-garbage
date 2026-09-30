import VerifiedGarbage.Proof.X448.X86_64.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X448 on x86-64: arithmetic steps

Untrusted: everything here is checked by Lean. Each short instruction block
is executed once symbolically, independently of its position in a field
operation. The bounds exclude overflow before interpreting machine words
as natural numbers.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

theorem and28 (x : BitVec 64) :
    (x &&& mask28.signExtend 64).toNat = x.toNat % radix := by
  rw [BitVec.toNat_and, show (mask28.signExtend 64).toNat = 2 ^ 28 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem shr28 (x : BitVec 64) : (x >>> 28).toNat = x.toNat / radix := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

/-- A carry step writes the low 28 bits and retains the high bits in `rcx`. -/
theorem carryStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 8 * i + 8 ≤ 8192) (ha : a + 8 * i + 8 ≤ 8192)
    (hb : (word s.mem base (a + 8 * i)).toNat + (s.gpr .rcx).toNat < 2 ^ 64) :
    let v := (word s.mem base (a + 8 * i)).toNat + (s.gpr .rcx).toNat
    WP isa (.block (carryStep o a i)) s fun s' =>
      (s'.gpr .rcx).toNat = v / radix ∧
      s'.mem = s.mem.writeW (off base (o + 8 * i)) (BitVec.ofNat 64 (v % radix)) ∧
      Keeps [.rax, .rcx, .rdx] s s' := by
  intro v
  have w := hs.write ho
  have l := hs.read ha
  apply WP.of_runBlock
  simp only [carryStep, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, l,
    Option.map_some, Option.bind_some, execAlu, execShift, ea_sc, State.load64,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, hs.rdi, State.store64, w, ite_true,
    ite_false, reduceCtorEq, Nat.reduceLeDiff, and_self, RegUpd.gpr_setFlags,
    Option.some.injEq, exists_eq_left']
  have hv : (word s.mem base (a + 8 * i) + s.gpr .rcx).toNat = v := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [shr28, hv]
  · apply congrArg (s.mem.writeW (off base (o + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    rw [and28, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v % radix) (by
      have := Nat.mod_lt v (show 0 < radix by decide)
      have : radix < 2 ^ 64 := by decide
      omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]

/-- A bounded multiply-add is an ordinary natural-number multiply-add. -/
theorem mul_add_nat (a b c : BitVec 64) (h : a.toNat * b.toNat + c.toNat < 2 ^ 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat) + c).toNat = a.toNat * b.toNat + c.toNat := by
  have hp : a.toNat * b.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt h]

/-- One row coefficient is updated; the inputs and every other word remain
available to subsequent steps. -/
theorem rowStep_ok {s : State} {base : Addr} (hs : Scr s base) {b i j : Nat}
    (hb : b + 8 * j + 8 ≤ 8192) (hi : i < 16) (hj : j < 16)
    (hr : s.gpr .r11 = off base (8 * i))
    (hv : (word s.mem base (b + 8 * j)).toNat * (s.gpr .rcx).toNat +
      (word s.mem base (ACC + 8 * (i + j))).toNat < 2 ^ 64) :
    let v := (word s.mem base (b + 8 * j)).toNat * (s.gpr .rcx).toNat +
      (word s.mem base (ACC + 8 * (i + j))).toNat
    WP isa (.block (rowStep b j)) s fun s' =>
      s'.mem = s.mem.writeW (off base (ACC + 8 * (i + j))) (BitVec.ofNat 64 v) ∧
      Keeps [.rax, .rdx] s s' := by
  intro v
  have hd : ACC + 8 * (i + j) + 8 ≤ 8192 := by simp only [ACC]; omega
  have l := hs.read hb
  have r := hs.read hd
  have w := hs.write hd
  apply WP.of_runBlock
  simp only [rowStep, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, l,
    Option.map_some, Option.bind_some, execMul, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_setFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.wr_arithFlags,
    State.ea, sc, at_, BitVec.ofInt_natCast, hs.rdi, hr, off, Offset.add_add,
    show 8 * i + (ACC + 8 * j) = ACC + 8 * (i + j) by omega,
    State.load64, State.store64, r, w, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (off base (ACC + 8 * (i + j))))
    apply BitVec.eq_of_toNat_eq
    rw [mul_add_nat _ _ _ hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
      hr.1, hr.2, ite_false]

end VG.Proof.X448.X86_64
