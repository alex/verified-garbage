import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep

/-! # Fixed scaling by public powers of two on ARM64 -/
namespace VG.Proof.Argon2.AArch64.MemoryInit
open VG VG.AArch64 VG.Impl.Argon2.AArch64

structure Scaled (s t : State) (r : Reg) (n : Nat) : Prop where
  value : t.gpr r = s.gpr r * BitVec.ofNat 64 (2 ^ n)
  other : ∀ q, q ≠ r → q ≠ .x15 → t.gpr q = s.gpr q
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem double_ok (s : State) (r : Reg) :
    WP isa (.block (Instructions.add r r)) s fun t =>
      t.gpr r = s.gpr r + s.gpr r ∧
      (∀ q, q ≠ r → q ≠ .x15 → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Instructions.add, Instructions.mark, Instructions.mov,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq hq' => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero, ite_self]
  · simp only [RegUpd.gpr_write, hq, hq', ite_false]

theorem scale_ok (s : State) (r : Reg) (n : Nat) :
    WP isa (.block (List.replicate n (Instructions.add r r)).flatten) s
      fun t => Scaled s t r n := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨by rw [Nat.pow_zero]; exact (BitVec.mul_one _).symm,
      fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    rw [WP.block_append_iff]
    refine (double_ok s r).mono ?_
    rintro a ⟨value, other, mem, rd, wr, sp⟩
    refine (ih a).mono ?_
    intro t ht
    refine ⟨?_, fun q hq hq' => (ht.other q hq hq').trans (other q hq hq'),
      ht.mem.trans mem, ht.rd.trans rd, ht.wr.trans wr, ht.sp.trans sp⟩
    rw [ht.value, value, ← BitVec.mul_two, Nat.pow_succ, BitVec.ofNat_mul,
      BitVec.mul_assoc]
    exact congrArg (fun v => s.gpr r * v) (BitVec.mul_comm _ _)
end VG.Proof.Argon2.AArch64.MemoryInit
