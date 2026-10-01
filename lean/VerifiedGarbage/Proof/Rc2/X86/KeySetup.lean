import VerifiedGarbage.Proof.Rc2.X86.CopyKey
import VerifiedGarbage.Proof.Rc2.X86.FillKey
import VerifiedGarbage.Proof.Rc2.X86.DescendKey
import VerifiedGarbage.Proof.Rc2.X86.Mask

/-! # Key-expansion control and register setup -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

theorem cmp128_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .ecx (.imm 128)] s = some s' ∧
      zeroFlag s' = some ((s.gpr .ecx - 128) == 0) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  constructor
  · rfl
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem maybeFill_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length ≤ 128)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 key.length) (start : s.gpr .ecx = BitVec.ofNat 32 key.length)
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (addr32 (s.gpr .edi)) (fill key 0) key.length) :
    WP isa (.seq (.block [.alu .cmp .ecx (.imm 128)])
      (.ite .ne (.loop (.block fillKey) .ne) (.block []))) s (fun s' =>
        s'.gpr .ecx = 128 ∧ KeyFrame s s' ∧
        BytesPrefix s'.mem (addr32 (s.gpr .edi)) (fill key (128 - key.length)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmp128_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp [keyTemps]))
  have flag : zeroFlag s₁ = some (decide (key.length = 128)) := by
    rw [flag₁, start]
    exact congrArg some (counter_eq _ _ (by omega) (by decide))
  have ptr₁ := keep₁.reg .edi (by simp)
  by_cases he : key.length = 128
  · apply WP.ite false (by simp only [eval_nonzero, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨?_, frame₁, ?_⟩
      · rw [keep₁.reg .ecx (by simp), start, he]; rfl
      · rw [keep₁.mem]
        simpa only [he, Nat.sub_self] using initialPrefix
  · apply WP.ite true (by simp only [eval_nonzero, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (addr32 (s₁.gpr .edi)) (fill key 0) key.length := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (fillLoop_ok s₁ key ht (by omega) (by rw [ptr₁]; exact outFit)
        ((keep₁.reg .esi (by simp)).trans len) ((keep₁.reg .ecx (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨h₂.1, frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

theorem setReduction_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .esp + 12)) 4)
    (input : s.mem.readW (addr32 (s.gpr .esp + 12)) 32 = BitVec.ofNat 32 bits) :
    ∃ s', runBlock isa reduceSetup s = some s' ∧
      s'.gpr .esi = BitVec.ofNat 32 ((bits + 7) / 8) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (128 - (bits + 7) / 8) ∧ Keep [.esi, .ecx] s s' := by
  simp only [addr32, BitVec.ofNat_eq_ofNat] at *
  refine ⟨_, by
    simp (config := {decide := true}) only [reduceSetup, imm, memOp, State.ea, BitVec.ofNat_eq_ofNat, runBlock_cons,
      runStep_some, exec, execAlu, execShift, readSrc, State.load32, Option.bind_some,
      Option.map_some, gpr_setReg, readable, ite_true]
    rfl, ?_⟩
  have t8 : (s.mem.readW (addr32 (s.gpr .esp + 12)) 32 + 7#32) >>> 3 = BitVec.ofNat 32 ((bits + 7) / 8) := by
    change (s.mem.readW (BitVec.setWidth 64 (s.gpr .esp + 12#32)) 32 + 7#32) >>> 3 = _
    rw [input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    exact t8
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    change 128#32 - (s.mem.readW (addr32 (s.gpr .esp + 12)) 32 + 7#32) >>> 3 = _
    rw [t8]
    exact Offset.ofNat_sub_ofNat (by omega)
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem maybeDescend_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 ≤ 128)
    (outFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .esi = BitVec.ofNat 32 t8) (start : s.gpr .ecx = BitVec.ofNat 32 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (addr32 (s.gpr .edi)) l 128) :
    WP isa (.seq (.block [.alu .cmp .ecx (.imm 0)])
      (.ite .ne (.loop (.block descendKey) .ne) (.block []))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (addr32 (s.gpr .edi)) (descend l t8 (128 - t8)) 128) := by
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
  have ptr₁ := keep₁.reg .edi (by simp)
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
      have writes : ∀ i < 128, InRegions s₁.wr (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (addr32 (s₁.gpr .edi)) l 128 := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (descendLoop_ok s₁ l t8 ht (by omega) (by rw [ptr₁]; exact outFit)
        ((keep₁.reg .esi (by simp)).trans len) ((keep₁.reg .ecx (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

end VG.Proof.Rc2.X86
