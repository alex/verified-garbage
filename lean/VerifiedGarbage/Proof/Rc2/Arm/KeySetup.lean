import VerifiedGarbage.Proof.Rc2.Arm.CopyKey
import VerifiedGarbage.Proof.Rc2.Arm.FillKey
import VerifiedGarbage.Proof.Rc2.Arm.DescendKey
import VerifiedGarbage.Proof.Rc2.Arm.Mask

/-! # Key-expansion control and register setup -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

theorem cmp128_ok (s : State) :
    ∃ s', runBlock isa [.cmp .r0 (.imm 128)] s = some s' ∧
      zeroFlag s' = some ((s.gpr .r0 - 128) == 0) ∧ Keep [] s s' := by
  refine ⟨subFlags s (s.gpr .r0) 128, ?_, ?_⟩
  · simp (config := {decide := true}) only [runBlock_cons, exec, Op2.eval, Option.map_some,
      ite_true, runStep_some, runBlock_nil]
  constructor
  · rfl
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem maybeFill_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length ≤ 128)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r5 = BitVec.ofNat 32 key.length) (start : s.gpr .r0 = BitVec.ofNat 32 key.length)
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (State.addr (s.gpr .r6)) (fill key 0) key.length) :
    WP isa (.seq (.block [.cmp .r0 (.imm 128)])
      (.ite .ne (.loop (.block fillKey) .ne) (.block []))) s (fun s' =>
        s'.gpr .r0 = 128 ∧ KeyFrame s s' ∧
        BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill key (128 - key.length)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmp128_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp [keyTemps]))
  have flag : zeroFlag s₁ = some (decide (key.length = 128)) := by
    rw [flag₁, start]
    exact congrArg some (counter_eq _ _ (by omega) (by decide))
  have ptr₁ := keep₁.reg .r6 (by simp)
  by_cases he : key.length = 128
  · apply WP.ite false (by simp only [eval_nonzero, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨?_, frame₁, ?_⟩
      · rw [keep₁.reg .r0 (by simp), start, he]; rfl
      · rw [keep₁.mem]
        simpa only [he, Nat.sub_self] using initialPrefix
  · apply WP.ite true (by simp only [eval_nonzero, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (State.addr (s₁.gpr .r6) + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (State.addr (s₁.gpr .r6)) (fill key 0) key.length := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (fillLoop_ok s₁ key ht (by omega) (by rw [ptr₁]; exact outFit)
        ((keep₁.reg .r5 (by simp)).trans len) ((keep₁.reg .r0 (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨h₂.1, frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

theorem setReduction_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .r7 = BitVec.ofNat 32 bits) :
    ∃ s', runBlock isa reduceSetup s = some s' ∧
      s'.gpr .r1 = BitVec.ofNat 32 ((bits + 7) / 8) ∧
      s'.gpr .r0 = BitVec.ofNat 32 (128 - (bits + 7) / 8) ∧ Keep [.r1, .r0] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [reduceSetup, imm, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, Option.map_some,
      gpr_setReg, ite_true, ite_false]
    rfl, ?_⟩
  have t8 : (s.gpr .r7 + 7#32) >>> 3 = BitVec.ofNat 32 ((bits + 7) / 8) := by
    rw [input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    exact t8
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    change 128#32 - (s.gpr .r7 + 7#32) >>> 3 = _
    rw [t8]
    exact Offset.ofNat_sub_ofNat (by omega)
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

theorem maybeDescend_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 ≤ 128)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r1 = BitVec.ofNat 32 t8) (start : s.gpr .r0 = BitVec.ofNat 32 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (State.addr (s.gpr .r6)) l 128) :
    WP isa (.seq (.block [.cmp .r0 (.imm 0)])
      (.ite .ne (.loop (.block descendKey) .ne) (.block []))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (State.addr (s.gpr .r6)) (descend l t8 (128 - t8)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpZero_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp [keyTemps]))
  have flag : zeroFlag s₁ = some (decide (t8 = 128)) := by
    rw [flag₁, start]
    have eqZero := counter_eq (128 - t8) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 32 (128 - t8) == 0#32) = _
    rw [eqZero]
    have he : 128 - t8 = 0 ↔ t8 = 128 := by omega
    simp only [he]
  have ptr₁ := keep₁.reg .r6 (by simp)
  by_cases he : t8 = 128
  · apply WP.ite false (by simp only [eval_nonzero, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨frame₁, ?_⟩
      rw [keep₁.mem, he]
      exact initialPrefix
  · apply WP.ite true (by simp only [eval_nonzero, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (State.addr (s₁.gpr .r6) + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (State.addr (s₁.gpr .r6)) l 128 := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (descendLoop_ok s₁ l t8 ht (by omega) (by rw [ptr₁]; exact outFit)
        ((keep₁.reg .r1 (by simp)).trans len) ((keep₁.reg .r0 (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

end VG.Proof.Rc2.Arm
