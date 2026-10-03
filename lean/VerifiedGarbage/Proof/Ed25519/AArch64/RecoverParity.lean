import VerifiedGarbage.Impl.Ed25519.AArch64.FieldCheck
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Impl.Ed25519.AArch64.RecoverSign

/-! Merged from `Proof.Ed25519.AArch64.FieldCheck`. -/
section
/-! Compare field elements through canonical representatives. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

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
      (t.gpr .x8 == 0) = decide (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = 0) ∧
      Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [wordsZero, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨wordsZero_flag _ _ _ _, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem fieldZero_ok {s : State} {base : Addr} (hs : Scr s base) (a : Slot) :
    WP isa (.block (fieldZero a)) s fun t =>
      (t.gpr .x8 == 0) = decide (env s.mem base a = 0) ∧ Keep base s t ∧ t.mem = s.mem := by
  rw [fieldZero, WP.block_append_iff]
  refine WP.mono (freezeField_ok hs a) fun u ⟨uv, ku⟩ => ?_
  refine WP.mono (wordsZero_ok u) fun t ⟨tz, kt⟩ => ?_
  refine ⟨?_, (Keep.of_keeps ku (by decide)).trans (Keep.of_keeps kt (by decide)), kt.mem.trans ku.mem⟩
  rw [tz, uv]
  have he : (env s.mem base a).val = 0 ↔ env s.mem base a = 0 := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Slot) :
    WP isa (.block (fieldEqual a b)) s fun t =>
      (t.gpr .x8 == 0) = decide (env s.mem base a = env s.mem base b) ∧ Keep base s t ∧
      ∀ i : Slot, i ≠ 21 → env t.mem base i = env s.mem base i := by
  rw [fieldEqual, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 21 a b] hs) fun u ⟨ku, vu⟩ => ?_
  refine WP.mono (fieldZero_ok (ku.scr hs) 21) fun t ⟨tz, kt, tm⟩ => ?_
  refine ⟨?_, ku.trans kt, ?_⟩
  · rw [tz, vu]
    change decide (env s.mem base a - env s.mem base b = 0) = _
    simp only [show ∀ u v : VG.Spec.X25519.Fe, u - v = 0 ↔ u = v from
      fun _ _ => ⟨fun _ => by grind, fun _ => by grind⟩]
  · intro i hi
    rw [tm, vu]
    change Function.update (env s.mem base) 21 (env s.mem base a - env s.mem base b) i = _
    exact Function.update_of_ne hi _ _

end VG.Proof.Ed25519.AArch64
end

/-! The public sign bit is compared to the canonical x-coordinate. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

def signWord (b : Bool) : BitVec 64 := if b then 1 else 0

theorem parity_flag (w : BitVec 64) (b : Bool) :
    ((w &&& BitVec.ofNat 64 1) ^^^ signWord b == 0) = ((w.toNat % 2 == 1) == b) := by
  have hw : w &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (BitVec.ofNat 64 1).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega)]
  rw [hw]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} (b : Bool) (hs : s.gpr .x1 = signWord b) :
    WP isa (.block recoverParity) s fun t =>
      (t.gpr .x8 == 0) = (((val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 == 1) == b)) ∧
      Keeps [.x9, .x8] s t := by
  have hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 = (s.gpr .x4).toNat % 2 := by
    simp only [val4]; omega
  apply WP.of_runBlock
  simp only [recoverParity, runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide, ite_true, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', hs, hv]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · exact parity_flag _ b
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.movz .w .x8 (if b then 1 else 0) 0]) s fun t =>
      t.gpr .x8 = signWord b ∧ Keeps [.x8] s t := by
  cases b <;> apply WP.of_runBlock <;>
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide, ite_true,
      Option.some.injEq, exists_eq_left']
  all_goals
    refine ⟨rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

end VG.Proof.Ed25519.AArch64
