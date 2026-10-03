import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Finalize

/-! # H′: arguments for a fixed workspace buffer -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure FixedArgs (s t : State) (offset size : Nat) : Prop where
  count : t.gpr .x1 = 0
  data : t.gpr .x2 = s.gpr .x24 + BitVec.ofNat 64 offset
  size : t.gpr .x3 = BitVec.ofNat 64 size
  other : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem fixedArgs_ok (s : State) (offset size : Nat) (ho : offset < 4096) (hn : size < 2 ^ 16) :
    WP isa (.block (fixedArgs offset size)) s fun t => FixedArgs s t offset size := by
  have hsize : (BitVec.ofNat 16 size).setWidth 64 = BitVec.ofNat 64 size := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega : size < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [fixedArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (16 * 0 : Nat) < 64 from by decide,
    ho, State.read, Size.bits, Nat.mul_zero, BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · exact hsize
  · simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

end VG.Proof.Argon2.AArch64.HPrime
