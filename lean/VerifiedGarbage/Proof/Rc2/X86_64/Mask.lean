import VerifiedGarbage.Proof.Rc2.X86_64.KeyLoop

/-! # Public effective-key mask selection -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem small_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 32 i).signExtend 64 = BitVec.ofNat 64 i := by
  rw [index_imm i hi]
  bv_omega

theorem cmpMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [.alu .cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))] s = some s' ∧
      s'.zf = some (s.gpr .r9 == BitVec.ofNat 64 (i + 1)) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  constructor
  · rw [zf_arithFlags, small_imm _ (by omega)]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem setMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [imm .rdx (2 ^ (i + 1) - 1)] s = some s' ∧
      s'.gpr .rdx = BitVec.ofNat 64 (2 ^ (i + 1) - 1) ∧ Keep [.rdx] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, exec, readSrc]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self]
    apply small_imm
    have bound : ∀ i < 7, 2 ^ (i + 1) - 1 < 256 := by decide
    exact bound i hi
  · exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem maskBranch_ok (s : State) (i : Nat) (hi : i < 7) :
    WP isa (.seq (.block [.alu .cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
      (.ite .e (.block [imm .rdx (2 ^ (i + 1) - 1)]) (.block []))) s (fun s' =>
        s'.gpr .rdx = (if s.gpr .r9 = BitVec.ofNat 64 (i + 1)
          then BitVec.ofNat 64 (2 ^ (i + 1) - 1) else s.gpr .rdx) ∧ Keep [.rdx] s s') := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpMask_ok s i hi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.ite (s.gpr .r9 == BitVec.ofNat 64 (i + 1)) (by exact flag₁)
  · intro he
    have eq := beq_iff_eq.mp he
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := setMask_ok s₁ i hi
    apply WP.of_runBlock
    refine ⟨s₂, run₂, ?_, ?_⟩
    · rw [ite_eq_left eq]; exact out₂
    · exact (keep₁.weaken (by simp)).trans keep₂
  · intro he
    have ne : s.gpr .r9 ≠ BitVec.ofNat 64 (i + 1) := by simpa using he
    apply WP.block_nil
    refine ⟨?_, keep₁.weaken (by simp)⟩
    rw [ite_eq_right ne]
    exact keep₁.reg .rdx (by simp)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.seq a b) c) s Q ↔ WP isa (.seq a (.seq b c)) s Q := by
  constructor
  · intro h
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)
  · intro h
    exact WP.seq (WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq_iff.mp h))

theorem maskBranches_ok (is : List Nat) (hi : ∀ i ∈ is, i < 7)
    (s : State) (k : Nat) (hk : k < 8) (index : s.gpr .r9 = BitVec.ofNat 64 k) :
    WP isa (is.foldr (fun i rest =>
      .seq (.block [.alu .cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
        (.seq (.ite .e (.block [imm .rdx (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))
      s (fun s' => s'.gpr .rdx = (if k ∈ is.map (· + 1) then
        BitVec.ofNat 64 (2 ^ k - 1) else s.gpr .rdx) ∧ Keep [.rdx] s s') := by
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
    have eq : BitVec.ofNat 64 k = BitVec.ofNat 64 (i + 1) ↔ k = i + 1 := by
      have bound := hi i List.mem_cons_self
      bv_omega
    simp only [eq, List.map_cons, List.mem_cons]
    by_cases he : k = i + 1
    · subst k; simp
    · by_cases hm : k ∈ is.map (· + 1) <;> simp [he, hm]

theorem maskStart_ok (s : State) :
    ∃ s', runBlock isa [rr .r9 .r15, .alu .and .r9 (.imm 7), imm .rdx 255] s = some s' ∧
      s'.gpr .r9 = s.gpr .r15 &&& 7 ∧ s'.gpr .rdx = 255 ∧ Keep [.rdx, .r9] s s' := by
  refine ⟨_, by
    simp only [rr, imm, runBlock_cons, exec, readSrc]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rfl
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem maskCode_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .r15 = BitVec.ofNat 64 bits) :
    WP isa maskCode s (fun s' =>
      (s'.gpr .rdx).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))) ∧
      Keep [.rdx, .r9] s s') := by
  rw [maskCode]
  apply WP.seq
  obtain ⟨s₁, run₁, index₁, mask₁, keep₁⟩ := maskStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have index : s₁.gpr .r9 = BitVec.ofNat 64 (bits % 8) := by
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

end VG.Proof.Rc2.X86_64
