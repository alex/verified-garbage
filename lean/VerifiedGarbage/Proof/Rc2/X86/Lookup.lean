import VerifiedGarbage.Impl.Rc2.X86.Lookup
import VerifiedGarbage.Proof.Rc2.Select32
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! # Correctness of baseline x86 RC2 lookup steps -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

/-- A register-only block preserves memory, regions, and other GPRs. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem index_imm (i : Nat) (hi : i < 256) :
    BitVec.ofNat 32 i = (BitVec.ofNat 8 i).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

theorem mask_neg (x : BitVec 32) : (x ^^^ 0xffffffff) + 1 = 0 - x := by
  change (x ^^^ BitVec.allOnes 32) + 1#32 = 0#32 - x
  rw [BitVec.xor_allOnes, ← BitVec.neg_eq_not_add, BitVec.zero_sub]

theorem piStep_ok (s : State) (x : Byte) (hx : s.gpr .eax = x.setWidth 32)
    (i : Nat) (hi : i < 256) :
    ∃ s', runBlock isa (piStep i) s = some s' ∧
      s'.gpr .ebx = s.gpr .ebx |||
        (if x.toNat = i then (Spec.Rc2.piTable.getD i 0).setWidth 32 else 0) ∧
      Keep [.ebx, .edx] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [piStep, selectMask, rr, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift,
      readSrc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      ite_true, ite_false]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rw [hx, index_imm i hi, mask_neg]
    change s.gpr .ebx |||
      ((0 - (((x.setWidth 32 ^^^ (BitVec.ofNat 8 i).setWidth 32) - 1) >>> 31)) &&&
        (Spec.Rc2.piTable.getD i 0).setWidth 32) = _
    rw [selectMask_eq]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.allOnes_and]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem piSteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 256)
    (s : State) (x : Byte) (hx : s.gpr .eax = x.setWidth 32) :
    WP isa (.block (is.flatMap piStep)) s (fun s' =>
      s'.gpr .ebx = s.gpr .ebx |||
        (if x.toNat ∈ is then (Spec.Rc2.piTable.getD x.toNat 0).setWidth 32 else 0) ∧
      Keep [.ebx, .edx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := piStep_ok s x hx i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .eax (by decide)).trans hx
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ hx₁)
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁]
    by_cases h : x.toNat = i
    · subst i
      by_cases hm : x.toNat ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x.toNat ∈ is <;> simp [h, hm]

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem piStart_ok (s : State) :
    ∃ s', runBlock isa [.alu .and .eax (.imm 255), imm .ebx 0] s = some s' ∧
      s'.gpr .eax = ((s.gpr .eax).setWidth 8).setWidth 32 ∧ s'.gpr .ebx = 0 ∧
      Keep [.eax, .ebx, .edx] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact maskByte _
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _

theorem piLookup_ok (s : State) :
    WP isa (.block piLookup) s (fun s' =>
      s'.gpr .eax = (Spec.Rc2.pi ((s.gpr .eax).setWidth 8)).setWidth 32 ∧
      Keep [.eax, .ebx, .edx] s s') := by
  rw [piLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := piStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piSteps_ok (List.range 256) (fun i hi => List.mem_range.mp hi)
    s₁ ((s.gpr .eax).setWidth 8) input₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .ebx = (Spec.Rc2.pi ((s.gpr .eax).setWidth 8)).setWidth 32 := by
    rw [h₂.1, zero₁]
    simp only [List.mem_range]
    rw [ite_eq_left ((s.gpr .eax).setWidth 8).isLt]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .eax (s₂.gpr .ebx), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.eax, .ebx, .edx] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _

end VG.Proof.Rc2.X86
