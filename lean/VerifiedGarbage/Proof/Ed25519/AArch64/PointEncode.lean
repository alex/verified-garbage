import VerifiedGarbage.Proof.Ed25519.AArch64.PointAffine
import VerifiedGarbage.Proof.Ed25519.AArch64.Freeze

/-! Untrusted: canonical point encoding in four machine words. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem freezeField_ok {s : State} {base : Addr} (hs : Scr s base) (a : Slot) :
    WP isa (.block (freeze (offset a))) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = (env s.mem base a).val ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x21, .x22, .x23, .x24] s t :=
  freeze_ok hs (slot_range a)

theorem sign_word (w : BitVec 64) :
    (w &&& 1) <<< 63 = BitVec.ofNat 64 ((w.toNat % 2) * 2 ^ 63) := by
  have he : w &&& 1 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega)]
  rw [he]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> decide

theorem pointSign_ok (s : State) :
    WP isa (.block pointSign) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 ((val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2) * 2 ^ 63) ∧
      Keeps [.x19, .x9] s t := by
  have hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 = (s.gpr .x4).toNat % 2 := by
    simp only [val4]; omega
  apply WP.of_runBlock
  simp only [pointSign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.w.bits from by decide, show (63 : Nat) < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [hv]; exact sign_word _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem encodeSign_ok (s : State) (x y : Nat) (hy : y < 2 ^ 255)
    (hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = y)
    (hs : s.gpr .x19 = BitVec.ofNat 64 ((x % 2) * 2 ^ 63)) :
    WP isa (.block [.add .x .x7 .x7 .x19]) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = y + (x % 2) * 2 ^ 255 ∧
      Keeps [.x7] s t := by
  have hb : (s.gpr .x7).toNat < 2 ^ 63 := by simp only [val4] at hv; omega
  have hm : ((x % 2) * 2 ^ 63) < 2 ^ 64 := by omega
  have ha : (s.gpr .x7 + s.gpr .x19).toNat = (s.gpr .x7).toNat + (x % 2) * 2 ^ 63 := by
    rw [hs, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [val4, ha] at hv ⊢; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem pointEncode_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa pointEncode s fun t => CounterKeep base s t ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val +
        ((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  rw [pointEncode]
  refine WP.seq (WP.mono (pointAffine_ok hs) fun a ⟨ka, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (freezeField_ok (ka.scr hs) 0) fun b ⟨bx, kb⟩ => ?_
  have kbe : CounterKeep base a b := CounterKeep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointSign_ok b) fun c ⟨cx, kc⟩ => ?_
  have kce : CounterKeep base b c := CounterKeep.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok (kce.scr (kbe.scr (ka.scr hs))) 1) fun d ⟨dy, kd⟩ => ?_
  have kde : CounterKeep base c d := CounterKeep.of_keeps kd (by decide)
  have dx : d.gpr .x19 = BitVec.ofNat 64
      (((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 63) := by
    rw [kd.gpr .x19 (by decide), cx, bx, ax]
  rw [kc.mem, kb.mem, ay] at dy
  refine WP.mono (encodeSign_ok d _ _ (by
    exact Nat.lt_trans (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).isLt
      (by decide : Spec.X25519.P < 2 ^ 255)) dy dx) fun t ⟨hv, kt⟩ => ?_
  exact ⟨(((ka.trans kbe).trans kce).trans kde).trans (CounterKeep.of_keeps kt (by decide)), hv⟩

end VG.Proof.Ed25519.AArch64
