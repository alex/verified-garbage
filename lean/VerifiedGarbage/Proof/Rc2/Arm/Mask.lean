import VerifiedGarbage.Proof.Rc2.Arm.KeyLoop

/-! # Public effective-key mask selection -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

theorem small_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 i).setWidth 32 = BitVec.ofNat 32 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem cmpMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [.cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))] s = some s' ∧
      zeroFlag s' = some (s.gpr .r9 == BitVec.ofNat 32 (i + 1)) ∧ Keep [] s s' := by
  have enc : encodable (BitVec.ofNat 32 (i + 1)) = true := by
    have fact : ∀ i < 7, encodable (BitVec.ofNat 32 (i + 1)) = true := by decide
    exact fact i hi
  refine ⟨subFlags s (s.gpr .r9) (BitVec.ofNat 32 (i + 1)), ?_, ?_⟩
  · simp only [runBlock_cons, exec, Op2.eval, enc, ite_true, Option.map_some, runStep_some, runBlock_nil]
  constructor
  · change some ((s.gpr .r9 - BitVec.ofNat 32 (i + 1)) == 0) = _
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem setMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [imm .r2 (2 ^ (i + 1) - 1)] s = some s' ∧
      s'.gpr .r2 = BitVec.ofNat 32 (2 ^ (i + 1) - 1) ∧ Keep [.r2] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, exec]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
    apply small_imm
    have bound : ∀ i < 7, 2 ^ (i + 1) - 1 < 256 := by decide
    exact bound i hi
  · exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; exact hr), rfl, rfl, rfl⟩

theorem maskBranch_ok (s : State) (i : Nat) (hi : i < 7) :
    WP isa (.seq (.block [.cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
      (.ite .eq (.block [imm .r2 (2 ^ (i + 1) - 1)]) (.block []))) s (fun s' =>
        s'.gpr .r2 = (if s.gpr .r9 = BitVec.ofNat 32 (i + 1)
          then BitVec.ofNat 32 (2 ^ (i + 1) - 1) else s.gpr .r2) ∧ Keep [.r2] s s') := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpMask_ok s i hi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.ite (s.gpr .r9 == BitVec.ofNat 32 (i + 1)) (by exact flag₁)
  · intro he
    have eq := beq_iff_eq.mp he
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := setMask_ok s₁ i hi
    apply WP.of_runBlock
    refine ⟨s₂, run₂, ?_, ?_⟩
    · rw [ite_eq_left eq]; exact out₂
    · exact (keep₁.weaken (by simp)).trans keep₂
  · intro he
    have ne : s.gpr .r9 ≠ BitVec.ofNat 32 (i + 1) := by simpa using he
    apply WP.block_nil
    refine ⟨?_, keep₁.weaken (by simp)⟩
    rw [ite_eq_right ne]
    exact keep₁.reg .r2 (by simp)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.seq a b) c) s Q ↔ WP isa (.seq a (.seq b c)) s Q := by
  constructor
  · intro h
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)
  · intro h
    exact WP.seq (WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq_iff.mp h))

theorem maskBranches_ok (is : List Nat) (hi : ∀ i ∈ is, i < 7)
    (s : State) (k : Nat) (hk : k < 8) (index : s.gpr .r9 = BitVec.ofNat 32 k) :
    WP isa (is.foldr (fun i rest =>
      .seq (.block [.cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
        (.seq (.ite .eq (.block [imm .r2 (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))
      s (fun s' => s'.gpr .r2 = (if k ∈ is.map (· + 1) then
        BitVec.ofNat 32 (2 ^ k - 1) else s.gpr .r2) ∧ Keep [.r2] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.foldr_cons, ← seq_assoc]
    apply WP.seq
    apply WP.mono (maskBranch_ok s i (hi i List.mem_cons_self))
    intro s₁ h₁
    have index₁ := (h₁.2.reg .r9 (by decide)).trans index
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ index₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₂.1, h₁.1, index]
    have eq : BitVec.ofNat 32 k = BitVec.ofNat 32 (i + 1) ↔ k = i + 1 := by
      have bound := hi i List.mem_cons_self
      bv_omega
    simp only [eq, List.map_cons, List.mem_cons]
    by_cases he : k = i + 1
    · subst k; simp
    · by_cases hm : k ∈ is.map (· + 1) <;> simp [he, hm]

theorem maskStart_ok (s : State) :
    ∃ s', runBlock isa ([rr .r9 .r7] ++ mask .r9 3 ++ [imm .r2 255]) s = some s' ∧
      s'.gpr .r9 = s.gpr .r7 &&& 7 ∧ s'.gpr .r2 = 255 ∧ Keep [.r2, .r9] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [rr, imm, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, gpr_setReg,
      ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
    rw [maskBits _ 3 (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
    change (s.gpr .r7).toNat % 8 % 2 ^ 32 = (s.gpr .r7).toNat &&& (2 ^ 3 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem maskCode_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .r7 = BitVec.ofNat 32 bits) :
    WP isa maskCode s (fun s' =>
      (s'.gpr .r2).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))) ∧
      Keep [.r2, .r9] s s') := by
  rw [maskCode]
  apply WP.seq
  obtain ⟨s₁, run₁, index₁, mask₁, keep₁⟩ := maskStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have index : s₁.gpr .r9 = BitVec.ofNat 32 (bits % 8) := by
    rw [index₁, input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    change bits % 2 ^ 32 &&& (2 ^ 3 - 1) = bits % 8 % 2 ^ 32
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
      ((if r ∈ (List.range 7).map (· + 1) then BitVec.ofNat 32 (2 ^ r - 1)
        else 255).setWidth 8) = BitVec.ofNat 8 (255 % 2 ^ (if r = 0 then 8 else r)) := by decide
  exact fact _ (Nat.mod_lt _ (by decide))

end VG.Proof.Rc2.Arm
