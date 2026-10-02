import VerifiedGarbage.Proof.AesGcm.X86_64.Run

/-!
# AES-GCM on x86-64: small blocks shared by the pieces

Untrusted: everything here is checked by Lean.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- `test r, r` sets ZF iff `r` holds 0. -/
theorem test_ok (s : State) (r : Reg) {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (decide (n = 0)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
  · rw [zf_arithFlags, h, and_self_beq hn]
  all_goals rfl

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

/-- Running a block with what is known of its result. -/
theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

/-- `rcx := min (16 - rbx, rbp)`. -/
theorem minLen_ok (s : State) {o n : Nat} (hbx : s.gpr .rbx = BitVec.ofNat 64 o)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 n) (ho : o ≤ 16) (hn : n < 2 ^ 64) :
    WP isa minLen s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min (16 - o) n) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (imm 16), .alu .sub .rcx (.reg .rbx),
      .alu .cmp .rbp (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (16 - o) ∧ s₁.cf = some (decide (n < 16 - o)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hbx, ofNat_sub ho (by decide)]
    · simp only [cf_arithFlags, hbp, hbx, setWidth_imm, ofNat_sub ho (by decide),
        toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (show 16 - o < 2 ^ 64 by omega),
        show (16 : Nat) % 2 ^ 32 = 16 from rfl]
    · intro r hr; simp [gpr_setReg, hr]
    all_goals rfl
  obtain ⟨hcx, hcf, hg, hm, hrd, hwr⟩ := h₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n < 16 - o)) (eval_b hcf) (fun ht => ?_) (fun hf => ?_)
  · refine WP.run (Q := fun s' => s' = s₁.setReg .rcx (s₁.gpr .rbp)) ⟨_, by xrun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r hr => ?_, hm, hrd, hwr⟩
    · simp only [gpr_setReg, ite_true, hg _ (by decide : Reg.rbp ≠ .rcx), hbp]
      simp at ht; rw [Nat.min_eq_right (by omega)]
    · simp only [gpr_setReg, hr, ite_false]; exact hg r hr
  · refine WP.block_nil ⟨?_, hg, hm, hrd, hwr⟩
    simp at hf; rw [hcx, Nat.min_eq_left (by omega)]

end VG.Proof.AesGcm.X86_64
