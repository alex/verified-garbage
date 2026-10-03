import VerifiedGarbage.Proof.Argon2.AArch64.Memory
import VerifiedGarbage.Impl.Argon2.AArch64.Parameters
import VerifiedGarbage.Proof.Argon2.AArch64.Divide
import VerifiedGarbage.Proof.Argon2.AArch64.DivideCT
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! Merged from `Proof.Argon2.AArch64.ParametersSteps`. -/
section
/-! Public frame loads and fixed arithmetic for the RFC's rounded memory dimensions. -/

namespace VG.Proof.Argon2.AArch64.Parameters

open VG VG.AArch64

theorem args_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 176) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8) :
    WP isa (.block Impl.Argon2.AArch64.Parameters.args) s fun t =>
      t.gpr .x0 = s.mem.readW (off (s.gpr .x19) 176) 64 ∧
      t.gpr .x1 = (s.mem.readW (off (s.gpr .x19) 184) 64) * 4 ∧ Divide.Keeps [.x0, .x1, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Parameters.args,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.add,
    Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read,
    addr, Size.bytes, Size.bits, show 0 < 4096 from by decide,
    show 176 % 8 = 0 ∧ 176 < 4096 * 8 from by decide,
    show 184 % 8 = 0 ∧ 184 < 4096 * 8 from by decide, and_self,
    memoryRead, lanesRead, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
    rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
    all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.AArch64.Parameters.finish) s fun t =>
    t.gpr .x21 = s.gpr .x5 * 4 ∧ Divide.Keeps [.x21, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Parameters.finish,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.add,
    Impl.Argon2.AArch64.Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, Size.bits, show 0 < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
    all_goals rfl

end VG.Proof.Argon2.AArch64.Parameters
end

/-! Exact rounded lane length using the verified fixed-time divider. -/

namespace VG.Proof.Argon2.AArch64.Parameters

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 176) 8
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8
  memoryWord : s.mem.readW (off (s.gpr .x19) 176) 64 = BitVec.ofNat 64 p.memory
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes
  positive : 0 < p.lanes
  memoryBound : p.memory < 2 ^ 32
  lanesBound : p.lanes < 2 ^ 24

def changed : List Reg := [.x0, .x1, .x15] ++ Divide.changed ++ [.x21, .x15]

theorem code_ok (s : State) (p : Params) (h : Ready p s) :
    WP isa Impl.Argon2.AArch64.Parameters.code s fun t =>
      t.gpr .x21 = BitVec.ofNat 64 p.laneLen ∧ Divide.Keeps changed s t := by
  unfold Impl.Argon2.AArch64.Parameters.code
  refine WP.seq ((args_ok s h.memoryRead h.lanesRead).mono ?_)
  rintro a ⟨memory, lanes, ka⟩
  have divisor : a.gpr .x1 = BitVec.ofNat 64 (4 * p.lanes) := by
    rw [lanes, h.lanesWord, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]
  have n : (a.gpr .x0).toNat = p.memory := by
    rw [memory, h.memoryWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.memoryBound (by decide))]
  have bound : 4 * p.lanes < 2 ^ 32 := by have lanesBound := h.lanesBound; omega
  have d : (a.gpr .x1).toNat = 4 * p.lanes := by
    rw [divisor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  refine WP.seq ((Divide.code_ok a (by rw [n]; exact h.memoryBound)
    (by rw [d]; have positive := h.positive; omega) (by rw [d]; exact bound)).mono ?_)
  rintro b ⟨quotient, _, kb⟩
  rw [n, d] at quotient
  have word : b.gpr .x5 = BitVec.ofNat 64 (p.memory / (4 * p.lanes)) := by
    rw [← quotient]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (finish_ok b).mono ?_
  rintro t ⟨value, kt⟩
  refine ⟨?_, (ka.mono (by simp [changed])).trans
    ((kb.mono (by
      intro r hr
      simp only [changed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl (Or.inr hr))).trans (kt.mono (by simp [changed])))⟩
  rw [value, word, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul,
    Nat.mul_comm, ← Proof.Argon2.laneLen_eq p h.positive]

end VG.Proof.Argon2.AArch64.Parameters
