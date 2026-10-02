import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Steps

/-! # Streaming RC2-CBC on x86-64: `init`'s length checks -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

/-- What `init` returns for invalid lengths, in `initWithEffectiveBits`'s
order, and 0 for valid ones. -/
def code (keyLen effectiveBits ivLen : Nat) : Nat :=
  if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1
  else if ¬(1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) then 2 else if ivLen ≠ 8 then 3 else 0

theorem code_le (a b c : Nat) : code a b c ≤ 3 := by
  unfold code; split <;> (try split) <;> (try split) <;> omega

theorem sub_one_lt (x : BitVec 64) {n : Nat} (hn : n < 2 ^ 64) :
    (x - 1).toNat < n ↔ 1 ≤ x.toNat ∧ x.toNat ≤ n := by
  have := x.isLt
  rw [BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

/-- `mov32 rax, c`, then `r10 = r - 1` compared with `n`: CF is set iff `r` is
in `1..=n`. -/
theorem checkRange_ok (s : State) (r : Reg) (hr : r ≠ .rax) (c n : Nat) (hc : c < 2 ^ 32) (hn : n < 2 ^ 63)
    (hs : (BitVec.signExtend 64 (BitVec.ofNat 32 n)).toNat = n) :
    ∃ s', runBlock isa [.mov32 .rax (.imm (BitVec.ofNat 32 c)), rr .r10 r, .alu .sub .r10 (.imm 1),
        .alu .cmp .r10 (.imm (BitVec.ofNat 32 n))] s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 c ∧ s'.cf = some (decide (1 ≤ (s.gpr r).toNat ∧ (s.gpr r).toNat ≤ n)) ∧
      Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      State.setReg32, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl⟩⟩
  · rw [gpr_arithFlags, gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags, gpr_setReg_of_ne _ _ (by decide),
      gpr_setReg_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
  · simp only [cf_arithFlags, gpr_setReg_self, gpr_setReg_of_ne _ _ hr, hs,
      show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, sub_one_lt _ (show n < 2 ^ 64 by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ hr'.2, gpr_setReg_of_ne _ _ hr'.1]

theorem checkIv_ok (s : State) :
    ∃ s', runBlock isa checkIv s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 3 ∧ s'.zf = some (decide ((s.gpr .r8).toNat = 8)) ∧ Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp only [checkIv, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      State.setReg32, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨by rw [gpr_arithFlags, gpr_setReg_self]; rfl, ?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl⟩⟩
  · rw [zf_arithFlags, gpr_setReg_of_ne _ _ (by decide), toNat_eq (s.gpr .r8),
      show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 by decide,
      Offset.ofNat_sub_ofNat_beq (s.gpr .r8).isLt (by decide), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (s.gpr .r8).isLt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ hr'.1]

theorem zero_ok (s : State) :
    ∃ s', runBlock isa [.mov32 .rax (.imm 0)] s = some s' ∧ s'.gpr .rax = BitVec.ofNat 64 0 ∧ Keep [.rax, .r10] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
    rfl, ?_⟩
  refine ⟨by rw [gpr_setReg_self]; rfl, ⟨fun r' hr' => ?_, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  simp only [gpr_setReg_of_ne _ _ hr'.1]

theorem keep_trans {s s' s'' : State} (h : Keep [.rax, .r10] s s') (h' : Keep [.rax, .r10] s' s'') :
    Keep [.rax, .r10] s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem checks_ok (s : State) :
    WP isa checks s fun t => Keep [.rax, .r10] s t ∧
      t.zf = some (decide (code (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat = 0)) ∧
      t.gpr .rax = BitVec.ofNat 64 (code (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat) := by
  refine WP.seq (WP.mono (Q := fun (t : State) => Keep [.rax, .r10] s t ∧
      t.gpr .rax = BitVec.ofNat 64 (code (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat)) ?_ ?_)
  · obtain ⟨s₁, run₁, rax₁, cf₁, keep₁⟩ := checkRange_ok s .rsi (by decide) 1 128 (by decide) (by decide) (by decide)
    refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
    refine WP.ite _ (by simp only [eval, cf₁]; rfl) (fun h => WP.block_nil ⟨keep₁, ?_⟩) (fun h => ?_)
    · rw [rax₁, code, ite_eq_left_of_eq_true _ _ (eq_true (by simp at h ⊢; omega))]
    obtain ⟨s₂, run₂, rax₂, cf₂, keep₂⟩ := checkRange_ok s₁ .rdx (by decide) 2 1024 (by decide) (by decide) (by decide)
    have hk : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 128 := by simpa using h
    rw [keep₁.reg _ (by decide)] at cf₂
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.ite _ (by simp only [eval, cf₂]; rfl) (fun h => WP.block_nil ⟨keep_trans keep₁ keep₂, ?_⟩)
      (fun h => ?_)
    · rw [rax₂, code, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h hk)), ite_eq_left_of_eq_true _ _ (eq_true (by simp at h ⊢; omega))]
    have he : 1 ≤ (s.gpr .rdx).toNat ∧ (s.gpr .rdx).toNat ≤ 1024 := by simpa using h
    obtain ⟨s₃, run₃, rax₃, zf₃, keep₃⟩ := checkIv_ok s₂
    rw [keep₂.reg _ (by decide), keep₁.reg _ (by decide)] at zf₃
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    refine WP.ite _ (by simp only [eval, zf₃]; rfl) (fun h => WP.block_nil ⟨keep_trans (keep_trans keep₁ keep₂) keep₃, ?_⟩)
      (fun h => ?_)
    · rw [rax₃, code, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h hk)), ite_eq_right_of_eq_false _ _ (eq_false (fun h => h he)), ite_eq_left_of_eq_true _ _ (eq_true (by simp at h ⊢; omega))]
    obtain ⟨s₄, run₄, rax₄, keep₄⟩ := zero_ok s₃
    refine WP.of_runBlock ⟨s₄, run₄, keep_trans (keep_trans (keep_trans keep₁ keep₂) keep₃) keep₄, ?_⟩
    rw [rax₄, code, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h hk)), ite_eq_right_of_eq_false _ _ (eq_false (fun h => h he)), ite_eq_right_of_eq_false _ _ (eq_false (by simp at h ⊢; omega))]
  · rintro t ⟨keep, rax⟩
    obtain ⟨t', run, zf, keep'⟩ := test_ok t .rax rax (by have := code_le (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .r8).toNat; omega)
    refine WP.of_runBlock ⟨t', run, ⟨fun r hr => (keep'.reg r (by simp)).trans (keep.reg r hr),
      keep'.mem.trans keep.mem, keep'.rd.trans keep.rd, keep'.wr.trans keep.wr⟩, zf, ?_⟩
    rw [keep'.reg _ (by simp), rax]

end VG.Proof.Rc2.X86_64.Stream
