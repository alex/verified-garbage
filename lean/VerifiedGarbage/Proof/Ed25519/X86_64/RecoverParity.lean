import VerifiedGarbage.Impl.Ed25519.X86_64.FieldCheck
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Impl.Ed25519.X86_64.RecoverSign

/-! Merged from `Proof.Ed25519.X86_64.FieldCheck`. -/
section
/-! Compare field elements through canonical representatives. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (val4 Keeps clob)

variable {fld : Arith} [EdArith fld]

theorem wordsZero_flag (a b c d : BitVec 64) :
    (((a ||| b) ||| c) ||| d == 0#64) = decide (val4 a b c d = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.or_eq_zero_iff, decide_eq_true_eq, val4]
  constructor
  · rintro ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩; rfl
  · intro h
    have ha : a.toNat = 0 := by omega
    have hb : b.toNat = 0 := by omega
    have hc : c.toNat = 0 := by omega
    have hd : d.toNat = 0 := by omega
    exact ⟨⟨⟨BitVec.eq_of_toNat_eq ha, BitVec.eq_of_toNat_eq hb⟩,
      BitVec.eq_of_toNat_eq hc⟩, BitVec.eq_of_toNat_eq hd⟩

theorem wordsZero_ok (s : State) :
    WP isa (.block wordsZero) s fun t =>
      t.zf = some (decide (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = 0)) ∧
      Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [wordsZero, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.and_self]
  refine ⟨wordsZero_flag _ _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem fieldZero_ok {s : State} {base : Addr} (hs : Scratch s base) (a : Slot) :
    WP isa (.block (fieldZero a)) s fun t =>
      t.zf = some (decide (env s.mem base a = 0)) ∧ Keep base s t ∧ t.mem = s.mem := by
  rw [fieldZero, WP.block_append_iff]
  refine WP.mono (freezeWide_ok hs a) fun u ⟨uv, ku⟩ => ?_
  refine WP.mono (wordsZero_ok u) fun t ⟨tz, kt⟩ => ?_
  refine ⟨?_, (Keep.of_keeps ku (by decide)).trans (Keep.of_keeps kt (by decide)), kt.2.1.trans ku.2.1⟩
  rw [tz, uv]
  have he : (env s.mem base a).val = 0 ↔ env s.mem base a = 0 := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {s : State} {base : Addr} (hs : Scratch s base) (a b : Slot) :
    WP isa (.block (fieldEqual fld a b)) s fun t =>
      t.zf = some (decide (env s.mem base a = env s.mem base b)) ∧ Keep base s t ∧
      ∀ i : Slot, i ≠ 21 → env t.mem base i = env s.mem base i := by
  rw [fieldEqual, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs [.sub 21 a b]) fun u ⟨ku, vu⟩ => ?_
  refine WP.mono (fieldZero_ok (hs.of_keep ku) 21) fun t ⟨tz, kt, tm⟩ => ?_
  refine ⟨?_, ku.trans kt, ?_⟩
  · rw [tz, vu]
    change some (decide (env s.mem base a - env s.mem base b = 0)) = _
    have e : env s.mem base a - env s.mem base b = 0 ↔ env s.mem base a = env s.mem base b :=
      ⟨fun h => by grind, fun h => by grind⟩
    simp only [e]
  · intro i hi
    rw [tm, vu]
    change Function.update (env s.mem base) 21 (env s.mem base a - env s.mem base b) i = _
    exact Function.update_of_ne hi _ _

end VG.Proof.Ed25519.X86_64
end

/-! The public sign bit is compared to the canonical x-coordinate. -/

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
