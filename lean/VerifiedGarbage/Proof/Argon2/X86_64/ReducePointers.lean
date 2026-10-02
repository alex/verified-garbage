import VerifiedGarbage.Impl.Argon2.X86_64.ReducePointers
import VerifiedGarbage.Proof.Argon2.X86_64.BlockAddress
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Argon2.FinalReduction

/-! The last-lane address calculation preserves all callee-saved registers. -/

namespace VG.Proof.Argon2.X86_64.ReducePointers

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.ReducePointers

def changed : List Reg := [.r8, .rax, .rcx, .rdx, .rsi, .rdi]

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 232) 8) :
    WP isa (.block Impl.Argon2.X86_64.ReducePointers.setup) s fun t =>
      t.gpr .r8 = s.mem.readW (off (s.gpr .rbp) 232) 64 ∧
      t.gpr .rax = s.gpr .rbx ∧ t.gpr .rcx = s.gpr .r12 - 1 ∧
      Divide.Keeps [.r8, .rax, .rcx] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.ReducePointers.setup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_at, read, ite_true, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]
  refine ⟨trivial, trivial, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.X86_64.ReducePointers.finish) s fun t =>
    t.gpr .rsi = s.gpr .rax ∧ t.gpr .rdi = s.gpr .r8 ∧ Divide.Keeps [.rsi, .rdi] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.ReducePointers.finish, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

theorem code_ok (s : State) (lane q : Nat) (positive : 0 < q)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 232) 8)
    (laneWord : s.gpr .rbx = BitVec.ofNat 64 lane) (lengthWord : s.gpr .r12 = BitVec.ofNat 64 q) :
    WP isa code s fun t =>
      t.gpr .rdi = s.mem.readW (off (s.gpr .rbp) 232) 64 ∧
      t.gpr .rsi = Proof.Argon2.matrixCell (s.mem.readW (off (s.gpr .rbp) 232) 64) ((lane + 1) * q - 1) ∧
      Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((setup_ok s read).mono ?_)
  rintro a ⟨base, lan, col, ka⟩
  have column : a.gpr .rcx = BitVec.ofNat 64 (q - 1) := by
    rw [col, lengthWord]
    exact Offset.ofNat_sub_ofNat (by omega : 1 ≤ q)
  refine WP.seq ((BlockAddress.code_nat_ok a lane (q - 1) q (lan.trans laneWord) column
    ((ka.regs .r12 (by decide)).trans lengthWord)).mono ?_)
  rintro b ⟨address, kb⟩
  refine (finish_ok b).mono ?_
  rintro t ⟨src, dest, kt⟩
  refine ⟨dest.trans ((kb.regs .r8 (by decide)).trans base), ?_, ?_⟩
  · rw [src, address, base]
    unfold Proof.Argon2.matrixCell
    have offset : lane * q + (q - 1) = (lane + 1) * q - 1 := by rw [Nat.add_mul, Nat.one_mul]; omega
    rw [offset]
  · exact (ka.mono (by simp [changed])).trans
      ((kb.mono (by simp [changed])).trans (kt.mono (by simp [changed])))

end VG.Proof.Argon2.X86_64.ReducePointers
