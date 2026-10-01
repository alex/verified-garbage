import VerifiedGarbage.Proof.Rc2.X86_64.CopyKey
import VerifiedGarbage.Proof.Rc2.X86_64.FillKey
import VerifiedGarbage.Proof.Rc2.X86_64.DescendKey
import VerifiedGarbage.Proof.Rc2.X86_64.Mask

/-! # Key-expansion control and register setup -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem cmp128_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp .rbx (.imm 128)] s = some s' ∧
      s'.zf = some ((s.gpr .rbx - 128) == 0) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  exact ⟨zf_arithFlags _ _ _ _, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩

theorem maybeFill_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length ≤ 128)
    (len : s.gpr .r13 = BitVec.ofNat 64 key.length) (start : s.gpr .rbx = BitVec.ofNat 64 key.length)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .r14) (fill key 0) key.length) :
    WP isa (.seq (.block [.alu .cmp .rbx (.imm 128)])
      (.ite .ne (.loop (.block fillKey) .ne) (.block []))) s (fun s' =>
        s'.gpr .rbx = 128 ∧ KeyFrame s s' ∧
        BytesPrefix s'.mem (s.gpr .r14) (fill key (128 - key.length)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmp128_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp))
  have flag : s₁.zf = some (decide (key.length = 128)) := by
    rw [flag₁, start]
    exact congrArg some (counter_eq _ _ (by omega) (by decide))
  have ptr₁ := keep₁.reg .r14 (by simp)
  by_cases he : key.length = 128
  · apply WP.ite false (by simp only [eval, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨?_, frame₁, ?_⟩
      · rw [keep₁.reg .rbx (by simp), start, he]; rfl
      · rw [keep₁.mem]
        simpa only [he, Nat.sub_self] using initialPrefix
  · apply WP.ite true (by simp only [eval, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .r14 + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (s₁.gpr .r14) (fill key 0) key.length := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (fillLoop_ok s₁ (by
        rw [keep₁.wr, keep₁.reg .r8 (by simp)]; exact hlookup) key ht (by omega)
        ((keep₁.reg .r13 (by simp)).trans len) ((keep₁.reg .rbx (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨h₂.1, frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

theorem setReduction_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .r15 = BitVec.ofNat 64 bits) :
    ∃ s', runBlock isa [rr .rbp .r15, .alu .add .rbp (.imm 7), .shift .shr .rbp 3,
      imm .rbx 128, .alu .sub .rbx (.reg .rbp)] s = some s' ∧
      s'.gpr .rbp = BitVec.ofNat 64 ((bits + 7) / 8) ∧
      s'.gpr .rbx = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧ Keep [.rbp, .rbx] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [rr, imm, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
    rfl, ?_⟩
  have t8 : (s.gpr .r15 + 7#64) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    rw [input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    exact t8
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    change 128#64 - (s.gpr .r15 + 7#64) >>> 3 = _
    rw [t8]
    exact Offset.ofNat_sub_ofNat (by omega)
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem maybeDescend_ok (s : State)
    (hlookup : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 ≤ 128)
    (len : s.gpr .rbp = BitVec.ofNat 64 t8) (start : s.gpr .rbx = BitVec.ofNat 64 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .r14) l 128) :
    WP isa (.seq (.block [.alu .cmp .rbx (.imm 0)])
      (.ite .ne (.loop (.block descendKey) .ne) (.block []))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (s.gpr .r14) (descend l t8 (128 - t8)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpZero_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp))
  have flag : s₁.zf = some (decide (t8 = 128)) := by
    rw [flag₁, start]
    have eqZero := counter_eq (128 - t8) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 64 (128 - t8) == 0#64) = _
    rw [eqZero]
    have he : 128 - t8 = 0 ↔ t8 = 128 := by omega
    simp only [he]
  have ptr₁ := keep₁.reg .r14 (by simp)
  by_cases he : t8 = 128
  · apply WP.ite false (by simp only [eval, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨frame₁, ?_⟩
      rw [keep₁.mem, he]
      exact initialPrefix
  · apply WP.ite true (by simp only [eval, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .r14 + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (s₁.gpr .r14) l 128 := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (descendLoop_ok s₁ (by
        rw [keep₁.wr, keep₁.reg .r8 (by simp)]; exact hlookup) l t8 ht (by omega)
        ((keep₁.reg .rbp (by simp)).trans len) ((keep₁.reg .rbx (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

end VG.Proof.Rc2.X86_64
