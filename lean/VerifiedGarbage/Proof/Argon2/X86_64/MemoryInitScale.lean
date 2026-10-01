import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitSteps

/-! # Fixed public scaling by powers of two using baseline additions -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64

structure Scaled (s t : State) (r : Reg) (n : Nat) : Prop where
  value : t.gpr r = s.gpr r * BitVec.ofNat 64 (2 ^ n)
  other : ∀ q, q ≠ r → t.gpr q = s.gpr q
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem double_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add r (.reg r)]) s fun t =>
      t.gpr r = s.gpr r + s.gpr r ∧ (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, ite_true]
  · simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, hr, ite_false]

theorem scale_ok (s : State) (r : Reg) (n : Nat) :
    WP isa (.block (List.replicate n (.alu .add r (.reg r)))) s fun t => Scaled s t r n := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨by rw [Nat.pow_zero]; exact (BitVec.mul_one _).symm,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    change WP isa (.block (([.alu .add r (.reg r)] : List Instr) ++
      List.replicate n (.alu .add r (.reg r)))) s _
    rw [WP.block_append_iff]
    refine (double_ok s r).mono ?_
    rintro a ⟨value, other, mem, rd, wr⟩
    refine (ih a).mono ?_
    intro t ht
    refine ⟨?_, fun q hq => (ht.other q hq).trans (other q hq),
      ht.mem.trans mem, ht.rd.trans rd, ht.wr.trans wr⟩
    rw [ht.value, value, ← BitVec.mul_two, Nat.pow_succ, BitVec.ofNat_mul,
      BitVec.mul_assoc]
    exact congrArg (fun v => s.gpr r * v) (BitVec.mul_comm _ _)

end VG.Proof.Argon2.X86_64.MemoryInit
