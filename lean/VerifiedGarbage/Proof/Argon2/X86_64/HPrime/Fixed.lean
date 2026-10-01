import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize

/-! # H′: arguments for a fixed workspace buffer -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure FixedArgs (s t : State) (offset size : Nat) : Prop where
  count : t.gpr .rsi = 0
  data : t.gpr .rdx = s.gpr .rbx + BitVec.ofNat 64 offset
  size : t.gpr .rcx = BitVec.ofNat 64 size
  other : ∀ r, r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem fixedArgs_ok (s : State) (offset size : Nat) (ho : offset < 2 ^ 31) (hn : size < 2 ^ 32) :
    WP isa (.block (fixedArgs offset size)) s fun t => FixedArgs s t offset size := by
  have hoff := Proof.MdStream.X86_64.sx_ofNat ho
  have hsize : (BitVec.ofNat 32 size).setWidth 64 = BitVec.ofNat 64 size := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega : size < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [fixedArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, State.setReg32, RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false, hoff]
  · simp only [RegUpd.gpr_setReg, ite_true, hsize]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, ite_false]

end VG.Proof.Argon2.X86_64.HPrime
