import VerifiedGarbage.Proof.X448.X86.Instr

/-!
# X448 on x86 (32-bit): carry steps

A bounded sum splits into a 16-bit digit and a carry before the next
coefficient is added.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem and16_nat (v : BitVec 32) : (v &&& (65535 : BitVec 32)).toNat = v.toNat % radix := by
  rw [BitVec.toNat_and, show (65535 : BitVec 32).toNat = 2 ^ 16 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem carryRaw_ok {s : State} {rb : Reg} {d : Nat} {a : Addr}
    (hr : rb ∉ [.eax, .ebx, .edx]) (ha : s.ea (at_ rb d) = a) (hw : InRegions s.wr a 4)
    (hb : (s.gpr .eax).toNat + (s.gpr .ebx).toNat < 2 ^ 32) :
    let v := (s.gpr .eax).toNat + (s.gpr .ebx).toNat
    WP isa (.block (VG.Impl.X448.X86.carryStep rb d)) s fun t =>
      (t.gpr .ebx).toNat = v / radix ∧
      t.mem = s.mem.writeW a (BitVec.ofNat 32 (v % radix)) ∧ Keeps [.eax, .ebx, .edx] s t := by
  intro v
  have hsum : (s.gpr .ebx + s.gpr .eax).toNat = v := by rw [BitVec.add_comm, BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  have mask : (s.gpr .ebx + s.gpr .eax) &&& (65535 : BitVec 32) = BitVec.ofNat 32 (v % radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [and16_nat, hsum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v % radix) (Nat.lt_trans (Nat.mod_lt v (by decide : 0 < radix)) (by decide : radix < 2 ^ 32))]
  have hn : 1 ≤ (16 : Nat) ∧ 16 ≤ 31 := by decide
  simp only [State.ea, at_] at ha
  apply WP.of_runBlock
  simp only [VG.Impl.X448.X86.carryStep, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.mem_setFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    State.ea, at_, hr.2.1, hr.2.2, hn, and_self,
    ite_true, ite_false, reduceCtorEq, ha, State.store32, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [BitVec.toNat_ushiftRight, hsum, Nat.shiftRight_eq_div_pow]; rfl
  · rw [mask]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.2.1, hr.2.2, ite_false]

/-- Load a coefficient and propagate its carry. -/
def carryBlock (o a i : Nat) : List Instr :=
  [ld .eax (a + 4 * i)] ++ VG.Impl.X448.X86.carryStep .edi (o + 4 * i)

theorem carryStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 4 * i + 4 ≤ 4096) (ha : a + 4 * i + 4 ≤ 4096)
    (hb : (word s.mem base (a + 4 * i)).toNat + (s.gpr .ebx).toNat < 2 ^ 32) :
    let v := (word s.mem base (a + 4 * i)).toNat + (s.gpr .ebx).toNat
    WP isa (.block (carryBlock o a i)) s fun t =>
      (t.gpr .ebx).toNat = v / radix ∧
      t.mem = s.mem.writeW (off base (o + 4 * i)) (BitVec.ofNat 32 (v % radix)) ∧
      Keeps [.eax, .ebx, .edx] s t := by
  intro v
  unfold carryBlock
  refine load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  refine WP.mono (carryRaw_ok (by decide) (ts.ea (by omega)) (ts.write (by omega))
    (by rw [ht.gpr, ht.other .ebx (by decide)]; exact hb)) fun u ⟨uc, um, uk⟩ => ?_
  rw [ht.gpr, ht.other .ebx (by decide)] at uc um
  exact ⟨uc, by rw [um, ht.mem], (ht.rest (by decide)).trans uk⟩

end VG.Proof.X448.X86
