import VerifiedGarbage.Proof.Rc2.AArch64.KeyLoop

/-! # Public effective-key mask selection -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

theorem small_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 i).setWidth 64 = BitVec.ofNat 64 i := by
  rw [index_imm i hi]
  bv_omega

theorem cmpMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [.subImm .x .x10 .x5 (i + 1)] s = some s' ∧
      zeroFlag s' = some (s.gpr .x5 == BitVec.ofNat 64 (i + 1)) ∧ Keep [.x10] s s' := by
  have bound : i + 1 < 4096 := by omega
  refine ⟨s.write .x .x10 (s.gpr .x5 - BitVec.ofNat 64 (i + 1)), ?_, ?_⟩
  · simp only [runBlock_cons, exec, bound, ite_true, State.read, BitVec.setWidth_eq,
      runStep_some, runBlock_nil]
  constructor
  · simp only [zeroFlag, gpr_write_self, BitVec.setWidth_eq]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega
  · exact ⟨fun r hr => gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem setMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [imm .x2 (2 ^ (i + 1) - 1)] s = some s' ∧
      s'.gpr .x2 = BitVec.ofNat 64 (2 ^ (i + 1) - 1) ∧ Keep [.x2, .x10] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, exec]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq, Nat.mul_zero, BitVec.shiftLeft_zero]
    apply small_imm
    have bound : ∀ i < 7, 2 ^ (i + 1) - 1 < 256 := by decide
    exact bound i hi
  · exact ⟨fun r hr => gpr_write_of_ne _ _ _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.1), rfl, rfl, rfl⟩

theorem maskBranch_ok (s : State) (i : Nat) (hi : i < 7) :
    WP isa (.seq (.block [.subImm .x .x10 .x5 (i + 1)])
      (.ite (.zero .x .x10) (.block [imm .x2 (2 ^ (i + 1) - 1)]) (.block []))) s (fun s' =>
        s'.gpr .x2 = (if s.gpr .x5 = BitVec.ofNat 64 (i + 1)
          then BitVec.ofNat 64 (2 ^ (i + 1) - 1) else s.gpr .x2) ∧ Keep [.x2, .x10] s s') := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpMask_ok s i hi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.ite (s.gpr .x5 == BitVec.ofNat 64 (i + 1)) (by exact flag₁)
  · intro he
    have eq := beq_iff_eq.mp he
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := setMask_ok s₁ i hi
    apply WP.of_runBlock
    refine ⟨s₂, run₂, ?_, ?_⟩
    · rw [ite_eq_left eq]; exact out₂
    · exact (keep₁.weaken (by simp)).trans keep₂
  · intro he
    have ne : s.gpr .x5 ≠ BitVec.ofNat 64 (i + 1) := by simpa using he
    apply WP.block_nil
    refine ⟨?_, keep₁.weaken (by simp)⟩
    rw [ite_eq_right ne]
    exact keep₁.reg .x2 (by simp)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.seq a b) c) s Q ↔ WP isa (.seq a (.seq b c)) s Q := by
  constructor
  · intro h
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)
  · intro h
    exact WP.seq (WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq_iff.mp h))

theorem maskBranches_ok (is : List Nat) (hi : ∀ i ∈ is, i < 7)
    (s : State) (k : Nat) (hk : k < 8) (index : s.gpr .x5 = BitVec.ofNat 64 k) :
    WP isa (is.foldr (fun i rest =>
      .seq (.block [.subImm .x .x10 .x5 (i + 1)])
        (.seq (.ite (.zero .x .x10) (.block [imm .x2 (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))
      s (fun s' => s'.gpr .x2 = (if k ∈ is.map (· + 1) then
        BitVec.ofNat 64 (2 ^ k - 1) else s.gpr .x2) ∧ Keep [.x2, .x10] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.foldr_cons, ← seq_assoc]
    apply WP.seq
    apply WP.mono (maskBranch_ok s i (hi i List.mem_cons_self))
    intro s₁ h₁
    have index₁ := (h₁.2.reg .x5 (by decide)).trans index
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ index₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₂.1, h₁.1, index]
    have eq : BitVec.ofNat 64 k = BitVec.ofNat 64 (i + 1) ↔ k = i + 1 := by
      have bound := hi i List.mem_cons_self
      bv_omega
    simp only [eq, List.map_cons, List.mem_cons]
    by_cases he : k = i + 1
    · subst k; simp
    · by_cases hm : k ∈ is.map (· + 1) <;> simp [he, hm]

theorem maskStart_ok (s : State) :
    ∃ s', runBlock isa ([rr .x5 .x22] ++ mask .x5 3 ++ [imm .x2 255]) s = some s' ∧
      s'.gpr .x5 = s.gpr .x22 &&& 7 ∧ s'.gpr .x2 = 255 ∧ Keep [.x2, .x5, .x10] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [rr, imm, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read, gpr_write,
      BitVec.setWidth_eq, BitVec.add_zero, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, ite_true]
    rw [maskBits _ 3 (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
    change (s.gpr .x22).toNat % 8 % 2 ^ 64 = (s.gpr .x22).toNat &&& (2 ^ 3 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2.1, ite_false]
    · rfl
    · rfl
    · rfl

theorem maskCode_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .x22 = BitVec.ofNat 64 bits) :
    WP isa maskCode s (fun s' =>
      (s'.gpr .x2).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))) ∧
      Keep [.x2, .x5, .x10] s s') := by
  rw [maskCode]
  apply WP.seq
  obtain ⟨s₁, run₁, index₁, mask₁, keep₁⟩ := maskStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have index : s₁.gpr .x5 = BitVec.ofNat 64 (bits % 8) := by
    rw [index₁, input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    change bits % 2 ^ 64 &&& (2 ^ 3 - 1) = bits % 8 % 2 ^ 64
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  apply WP.mono (maskBranches_ok (List.range 7) (by simp)
    s₁ (bits % 8) (Nat.mod_lt _ (by decide)) index)
  intro s₂ h₂
  refine ⟨?_, keep₁.trans (h₂.2.weaken (by simp))⟩
  rw [h₂.1, mask₁]
  have exponent : 8 + bits - 8 * ((bits + 7) / 8) = if bits % 8 = 0 then 8 else bits % 8 := by
    split <;> omega
  rw [exponent]
  have fact : ∀ r < 8,
      ((if r ∈ (List.range 7).map (· + 1) then BitVec.ofNat 64 (2 ^ r - 1)
        else 255).setWidth 8) = BitVec.ofNat 8 (255 % 2 ^ (if r = 0 then 8 else r)) := by decide
  exact fact _ (Nat.mod_lt _ (by decide))

end VG.Proof.Rc2.AArch64
