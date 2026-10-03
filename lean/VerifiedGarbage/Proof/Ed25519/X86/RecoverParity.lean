import VerifiedGarbage.Impl.Ed25519.X86.FieldCheck
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Impl.Ed25519.X86.RecoverSign
import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign

/-! Merged from `Proof.Ed25519.X86.FieldCheck`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

def orWords (m : Mem) (x : BitVec 32) (o : Nat) : Nat → BitVec 32
  | 0 => 0
  | n + 1 => orWords m x o n ||| wd m x (o + 4 * n)

theorem orWords_zero (m : Mem) (x : BitVec 32) (o n : Nat) :
    orWords m x o n = 0#32 ↔ num (fun j => wv m x (o + 4 * j)) n = 0 := by
  induction n with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    change (orWords m x o n ||| wd m x (o + 4 * n) = 0#32) ↔ _
    rw [BitVec.or_eq_zero_iff, ih, num_succ]
    have hp : 0 < (2 ^ 32) ^ n := Nat.pow_pos (by decide)
    have hw : wd m x (o + 4 * n) = 0#32 ↔ wv m x (o + 4 * n) = 0 :=
      ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hw]
    constructor
    · rintro ⟨h, w⟩; rw [h, w]; rfl
    · intro h
      have hw' : wv m x (o + 4 * n) = 0 := by
        have := Nat.le_mul_of_pos_left (wv m x (o + 4 * n)) hp
        omega_using [h, this]
      exact ⟨by omega_using [h], hw'⟩

theorem wordOr_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o j : Nat}
    (ho : o + 4 * j + 4 ≤ 8192) :
    WP isa (.block (wordOr o j)) s fun t => Keep s t ∧ t.mem = s.mem ∧
      t.gpr .eax = s.gpr .eax ||| wd s.mem x (o + 4 * j) := by
  refine Wp.wp_ldm hc.edi (hc.inRW ho (by decide)) fun a ha => ?_
  refine Wp.wp_or fun t ht => WP.block_nil ?_
  exact ⟨(updKeep ha).trans (updKeep ht), ht.mem.trans ha.mem,
    by rw [ht.gpr, ha.gpr, ha.other .eax (by decide)]⟩

theorem orPrefix_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat}
    (ho : o + 32 ≤ 8192) (hz : s.gpr .eax = 0) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap (wordOr o))) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .eax = orWords s.mem x o n
  | 0, _ => WP.block_nil ⟨Keep.refl _, rfl, hz⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (orPrefix_ok hc ho hz n (by omega_using [hn])) fun u ⟨ku, mu, vu⟩ => ?_)
    refine WP.mono (wordOr_ok (ku.ctx hc) (by omega_using [ho, hn])) fun t ⟨kt, mt, vt⟩ => ?_
    exact ⟨ku.trans kt, mt.trans mu, by rw [vt, mu, vu]; rfl⟩

theorem wordsZero_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {o : Nat} (ho : o + 32 ≤ 8192) :
    WP isa (.block (wordsZero o)) s fun t => Keep s t ∧ t.mem = s.mem ∧
      t.zf = some (decide (fe s.mem x o = 0)) := by
  rw [wordsZero, List.append_assoc, WP.block_append_iff]
  refine Wp.wp_movi fun a ha => WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (orPrefix_ok ((updKeep ha).ctx hc) ho ha.gpr 8 (Nat.le_refl _)) fun b ⟨kb, mb, vb⟩ => ?_
  refine Wp.wp_test fun t ht zt => WP.block_nil ?_
  refine ⟨((updKeep ha).trans kb).trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩,
    ht.mem.trans (mb.trans ha.mem), ?_⟩
  rw [zt, BitVec.and_self, vb, ha.mem]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  change (orWords s.mem x o 8 == 0) = true ↔ decide (fe s.mem x o = 0) = true
  rw [beq_iff_eq, decide_eq_true_eq]
  exact orWords_zero s.mem x o 8

theorem fieldZero_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (a : Slot) :
    WP isa (.block (fieldZero a)) s fun t => FieldKeep x s t ∧ env t.mem x = env s.mem x ∧
      t.zf = some (decide (env s.mem x a = 0)) := by
  rw [fieldZero, WP.block_append_iff]
  refine WP.mono (freezeField_ok hc a) fun u ⟨ku, eu, vu⟩ => ?_
  have ho : offset a + 32 ≤ 8192 := by have ha := a.isLt; simp only [offset]; omega_using [ha]
  refine WP.mono (wordsZero_ok (ku.ctx hc) ho) fun t ⟨kt, mt, zt⟩ => ?_
  refine ⟨ku.trans (FieldKeep.of_mem kt mt), by rw [mt, eu], ?_⟩
  rw [zt, vu]
  have he : (env s.mem x a).val = 0 ↔ env s.mem x a = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (a b : Slot) :
    WP isa (.block (fieldEqual a b)) s fun t => FieldKeep x s t ∧
      (∀ i : Slot, i ≠ 21 → env t.mem x i = env s.mem x i) ∧
      t.zf = some (decide (env s.mem x a = env s.mem x b)) := by
  rw [fieldEqual, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 21 a b] hc) fun u ⟨ku, eu⟩ => ?_
  refine WP.mono (fieldZero_ok (ku.ctx hc) 21) fun t ⟨kt, et, zt⟩ => ?_
  refine ⟨ku.trans kt, ?_, ?_⟩
  · intro i hi
    rw [et, eu]
    exact Function.update_of_ne hi _ _
  · rw [zt, eu]
    change some (decide (env s.mem x a - env s.mem x b = 0)) = _
    simp only [show ∀ u v : VG.Spec.X25519.Fe, u - v = 0 ↔ u = v from
      fun _ _ => ⟨fun _ => by grind, fun _ => by grind⟩]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def signWord (b : Bool) : BitVec 32 := BitVec.ofNat 32 b.toNat

theorem parity_eq (w : BitVec 32) (b : Bool) :
    ((w &&& 1) ^^^ signWord b == 0) = ((w.toNat % 2 == 1) == b) := by
  have he : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 32 by omega)]
  rw [he]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa (.block recoverParity) s fun t => FieldKeep x s t ∧ t.mem = s.mem ∧
      t.zf = some ((fe s.mem x 64 % 2 == 1) == b) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha => ?_
  refine Wp.wp_andi fun c hc' => Wp.wp_xor fun d hd => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have kk := (updKeep ha).trans ((updKeep hc').trans (updKeep hd))
  have kt : Keep s t := kk.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩
  have mt : t.mem = s.mem := by rw [ht.mem, hd.mem, hc'.mem, ha.mem]
  refine ⟨FieldKeep.of_mem kt mt, mt, ?_⟩
  rw [zt, BitVec.and_self, hd.gpr, hc'.gpr, hc'.other .esi (by decide), ha.other .esi (by decide), hb, ha.gpr]
  rw [field_parity]
  exact congrArg some (parity_eq _ b)

theorem returnFlag_ok (s : State) (x : BitVec 32) (b : Bool) :
    WP isa (.block [.mov .eax (.imm (signWord b))]) s fun t =>
      FieldKeep x s t ∧ t.mem = s.mem ∧ t.gpr .eax = signWord b := by
  refine Wp.wp_movi fun t ht => WP.block_nil ⟨FieldKeep.of_mem (updKeep ht) ht.mem, ht.mem, ht.gpr⟩

end VG.Proof.Ed25519.X86
