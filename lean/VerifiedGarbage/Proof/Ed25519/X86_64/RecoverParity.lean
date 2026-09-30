import VerifiedGarbage.Impl.Ed25519.X86_64.RecoverSign
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldCheck

/-! Untrusted: the public sign bit is compared to the canonical x-coordinate. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps)

def signWord (b : Bool) : BitVec 64 := if b then 1 else 0

theorem parity_flag (w : BitVec 64) (b : Bool) :
    ((w &&& (1 : BitVec 32).signExtend 64) ^^^ signWord b == 0) = ((w.toNat % 2 == 1) == b) := by
  have hw : w &&& (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega)]
  rw [hw]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} (b : Bool) (hs : s.gpr .rsi = signWord b) :
    WP isa (.block recoverParity) s fun t =>
      t.zf = some (((val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2 == 1) == b)) ∧
      Keeps [.rax] s t := by
  have hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2 = (s.gpr .r8).toNat % 2 := by
    simp only [val4]; omega
  apply WP.of_runBlock
  simp only [recoverParity, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.and_self, hs, parity_flag, hv]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.mov32 .rax (.imm (if b then 1 else 0))]) s fun t =>
      t.gpr .rax = signWord b ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases b <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact RegUpd.gpr_setReg_of_ne _ _ hr

theorem testSign_ok {s : State} (b : Bool) (hs : s.gpr .rsi = signWord b) :
    WP isa (.block [.alu .test .rsi (.reg .rsi)]) s fun t => t.zf = some (!b) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hs]
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  cases b <;> rfl

end VG.Proof.Ed25519.X86_64
