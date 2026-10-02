import VerifiedGarbage.Proof.X448.AArch64.Step

/-! Untrusted: carry a coefficient directly from its register. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem pointwiseCarry_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 16)
    (hb : (s.gpr .x4).toNat + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := (s.gpr .x4).toNat + (s.gpr .x6).toNat
    WP isa (.block (Pointwise.carry i)) s fun s' =>
      (s'.gpr .x6).toNat = v / radix ∧
      s'.mem = s.mem.writeW (off base (TMP + 8 * i)) (BitVec.ofNat 64 (v % radix)) ∧
      Keeps [.x4, .x6, .x5] s s' := by
  intro v
  have ho : TMP + 8 * i + 8 ≤ 8192 := by simp only [TMP]; omega
  have w := hs.write ho
  have oe : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 4096 * 8 := ⟨by simp only [TMP]; omega, by omega⟩
  apply WP.of_runBlock
  simp only [Pointwise.carry, st, runBlock_cons, runStep_some, runBlock_nil, exec,
    Size.bytes, Size.bits, addr, oe, State.read, State.store, hs.x3, hs.mask, w,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write,
    BitVec.setWidth_eq, Option.bind_some,
    and_self, ite_true, ite_false, reduceCtorEq, Nat.reduceLT, Nat.reduceMul,
    write8_eq, Option.some.injEq, exists_eq_left']
  have hv : (s.gpr .x4 + s.gpr .x6).toNat = v := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [shr28, hv]
  · apply congrArg (s.mem.writeW (off base (TMP + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    rw [and28, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v % radix) (by
      have := Nat.mod_lt v (show 0 < radix by decide)
      have : radix < 2 ^ 64 := by decide
      omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.X448.AArch64
