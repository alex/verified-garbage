import VerifiedGarbage.Proof.AesGcm.Arm.Loops

/-!
# AES-GCM on ARMv7: small blocks shared by the pieces

Untrusted: everything here is checked by Lean. `cmp r, #0` (`cmp0_ok`), and
`minLen`: `r3 := min (16 - r6, r5)`, from the carry of a comparison
(`minLen_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm

/-- `cmp r, #0` sets `Z` iff `r` holds 0. -/
theorem cmp0_ok (s : State) (r : Reg) {n : Nat} (h : s.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.cmp r (imm 0)] s = some s' ∧ s'.z = decide (n = 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [z_subFlags, h]; rw [z_cmp hn (by decide)]
  all_goals rfl

/-- `cmp r, #k`. -/
theorem cmpk_ok (s : State) (r : Reg) {n k : Nat} (h : s.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (hk : k < 2 ^ 32) (he : encodable (BitVec.ofNat 32 k) = true) :
    ∃ s', runBlock isa [.cmp r (imm k)] s = some s' ∧ s'.z = decide (n = k) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [he], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [z_subFlags, h]; rw [z_cmp hn hk]
  all_goals rfl

/-- What a block that keeps everything but some registers leaves. -/
structure Keeps (s s' : State) : Prop where
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, rfl⟩

theorem adc_c (b : Bool) : (0 : BitVec 32) + BitVec.ofNat 32 0 + (if b = true then 1 else 0) =
    if b then 1 else 0 := by cases b <;> rfl

/-- `r3 := min (16 - r6, r5)`. -/
theorem minLen_ok (s : State) {o n : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 o)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (ho : o ≤ 16) (hn : n < 2 ^ 32) :
    WP isa minLen s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (min (16 - o) n) ∧
      (∀ r, r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.mov .r3 (imm 16), .dp .sub .r3 .r3 (.reg .r6), .cmp .r5 (.reg .r3),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r3 = BitVec.ofNat 32 (16 - o) ∧ s₁.z = !decide (16 - o ≤ n) ∧
      (∀ r, r ≠ .r3 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h6, ofNat_sub32 ho (by decide)]
    · simp only [z_subFlags, c_subFlags, gpr_setReg, z_setReg, c_setReg, ite_true, ite_false, reduceCtorEq,
        h5, h6, ofNat_sub32 ho (by decide), toNat32 hn, toNat32 (show 16 - o < 2 ^ 32 by omega)]
      cases decide (16 - o ≤ n) <;> rfl
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hr3, hz, hg, hk⟩ := h₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (!decide (16 - o ≤ n)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · refine WP.run (Q := fun s' => s' = s₁.setReg .r3 (s₁.gpr .r5)) ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r h₁ h₂ => ?_, hk.trans ⟨rfl, rfl, rfl, rfl⟩⟩
    · rw [gpr_setReg_self, hg .r5 (by decide) (by decide), h5]
      simp at ht; rw [Nat.min_eq_right (by omega)]
    · simp only [gpr_setReg, h₁, ite_false]; exact hg r h₁ h₂
  · refine WP.block_nil ⟨?_, hg, hk⟩
    simp at hf; rw [hr3, Nat.min_eq_left (by omega)]

end VG.Proof.AesGcm.Arm
