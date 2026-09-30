import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Proof.X25519.X86_64.Freeze

/-! Untrusted: canonical point encoding in four machine words. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Keeps val4 fe)

theorem freezeWide_ok {s : State} {base : Addr} (hs : Scratch s base) (a : Slot) :
    WP isa (.block (VG.Impl.X25519.X86_64.freeze (offset a))) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = (env s.mem base a).val ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax, .rcx, .rdx] s t := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hv, hk⟩ := Proof.X25519.X86_64.freeze_ok hn (a := offset a) (by simp only [offset]; omega)
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hv, hk.1, hk.2.1, rfl, rfl⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem sign_word (w : BitVec 64) :
    (w &&& (1 : BitVec 32).signExtend 64).rotateRight 1 = BitVec.ofNat 64 ((w.toNat % 2) * 2 ^ 63) := by
  have he : w &&& (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega)]
  rw [he]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> decide

theorem pointSign_ok (s : State) :
    WP isa (.block pointSign) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 ((val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2) * 2 ^ 63) ∧
      Keeps [.rbx] s t := by
  have hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) % 2 = (s.gpr .r8).toNat % 2 := by
    simp only [val4]; omega
  apply WP.of_runBlock
  simp only [pointSign, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    execShift, show 1 ≤ 1 ∧ 1 ≤ 63 from by decide, and_self, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hv]; exact sign_word _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr, ite_false]

theorem encodeSign_ok (s : State) (x y : Nat) (hy : y < 2 ^ 255)
    (hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = y)
    (hs : s.gpr .rbx = BitVec.ofNat 64 ((x % 2) * 2 ^ 63)) :
    WP isa (.block [.alu .add .r11 (.reg .rbx)]) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = y + (x % 2) * 2 ^ 255 ∧
      Keeps [.r11] s t := by
  have hb : (s.gpr .r11).toNat < 2 ^ 63 := by simp only [val4] at hv; omega
  have hm : ((x % 2) * 2 ^ 63) < 2 ^ 64 := by omega
  have ha : (s.gpr .r11 + s.gpr .rbx).toNat = (s.gpr .r11).toNat + (x % 2) * 2 ^ 63 := by
    rw [hs, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [val4, ha] at hv ⊢; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem pointEncode_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa pointEncode s fun t => RbxKeep base s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val +
        ((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  rw [pointEncode]
  refine WP.seq (WP.mono (pointAffine_ok hs) fun a ⟨ka, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (freezeWide_ok (ka.scratch hs) 0) fun b ⟨bx, kb⟩ => ?_
  have kbe : RbxKeep base a b := RbxKeep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointSign_ok b) fun c ⟨cx, kc⟩ => ?_
  have kce : RbxKeep base b c := RbxKeep.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freezeWide_ok (kce.scratch (kbe.scratch (ka.scratch hs))) 1) fun d ⟨dy, kd⟩ => ?_
  have kde : RbxKeep base c d := RbxKeep.of_keeps kd (by decide)
  have dx : d.gpr .rbx = BitVec.ofNat 64
      (((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 63) := by
    rw [kd.1 .rbx (by decide), cx, bx, ax]
  rw [kc.2.1, kb.2.1, ay] at dy
  refine WP.mono (encodeSign_ok d _ _ (by
    exact Nat.lt_trans (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).isLt
      (by decide : Spec.X25519.P < 2 ^ 255)) dy dx) fun t ⟨hv, kt⟩ => ?_
  exact ⟨(((ka.trans kbe).trans kce).trans kde).trans (RbxKeep.of_keeps kt (by decide)), hv⟩

end VG.Proof.Ed25519.X86_64
