import VerifiedGarbage.Proof.Ed25519.X86.PointPowersCounter

/-! Untrusted: write the current point, then advance one or sixteen doublings. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem IKeep.of_mem {x : BitVec 32} {s t : State} (h : Keep s t) (hm : t.mem = s.mem) :
    IKeep x s t := ⟨h.edi, h.esp, h.rd, h.wr, by rw [hm]; exact Frame.refl _ _⟩

theorem powerBatch_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hd : env s.mem x 16 = Spec.Ed25519.d) (batch : Bool) :
    WP isa (powerBatch batch) s fun t => IKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = powerPoint (point (env s.mem x) 0 1 2 3) (powerStride batch) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  cases batch with
  | true => exact double16_ok hc hd
  | false => exact WP.mono (pointDouble_ok hc hd) fun _ ⟨hk, hp, hh⟩ => ⟨IKeep.of_field hk, hp, hh⟩

theorem powersBody_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (start count j : Nat) (batch : Bool) (hj : j < count) (hc' : count ≤ 32)
    (hlo : 928 ≤ start) (hfit : start + 128 * count ≤ 8192)
    (hindex : wd s.mem x 24 = BitVec.ofNat 32 j) (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (powersBody start count batch) s fun t =>
      PowersKeep x (start + 128 * j) 128 s t ∧ wd t.mem x 24 = BitVec.ofNat 32 (j + 1) ∧
      isa.eval .ne t = some (!decide (j + 1 = count)) ∧
      point (env t.mem x) 0 1 2 3 = powerPoint (point (env s.mem x) 0 1 2 3) (powerStride batch) ∧
      tablePoint t.mem x (start + 128 * j) = point (env s.mem x) 0 1 2 3 ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.seq (WP.mono (powersLoad_ok hc) fun s₁ ⟨k₁, m₁, b₁⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (k₁.ctx hc) start j (by omega) (b₁.trans hindex)) fun s₂ ⟨k₂, m₂, p₂⟩ => ?_
  have c₂ := k₂.ctx (k₁.ctx hc)
  refine WP.mono (pointToTable_ok c₂ p₂ (by omega) (by omega)) fun s₃ ⟨k₃, p₃⟩ => ?_
  have c₃ := k₃.ctx c₂
  have e₃ : env s₃.mem x = env s.mem x := by
    rw [table_env hc.fit k₃.frame (by omega) (by omega), m₂, m₁]
  have i₃ : wd s₃.mem x 24 = BitVec.ofNat 32 j := by
    rw [wd_frame1 k₃.frame hc.fit (by omega) (by decide) (Or.inl (by omega)), m₂, m₁]
    exact hindex
  have pk₃ : PowersKeep x (start + 128 * j) 128 s s₃ :=
    ((PowersKeep.of_ikeep k₁ _ _).trans
      (PowersKeep.of_ikeep (IKeep.of_mem k₂ m₂) _ _)).trans (PowersKeep.of_copy k₃)
  refine WP.seq (WP.mono (powerBatch_ok c₃ (by rw [e₃]; exact hd) batch) fun s₄ ⟨k₄, p₄, h₄⟩ => ?_)
  refine WP.mono (powersNext_ok (k₄.ctx c₃) j count (start + 128 * j) 128 (by omega) (by omega)
    ((workspace_counter k₄ c₃).trans i₃)) fun s₅ ⟨k₅, i₅, z₅, f₅⟩ => ?_
  have e₅ : env s₅.mem x = env s₄.mem x := counter_env hc.fit f₅
  refine ⟨(pk₃.trans (PowersKeep.of_ikeep k₄ _ _)).trans k₅, i₅, z₅, ?_, ?_, ?_⟩
  · rw [e₅, p₄, e₃]
  · rw [tablePoint_frame hc.fit f₅ (by decide) (by omega) (Or.inr (by omega)),
      workspace_table k₄ c₃ _ (by omega) (by omega), p₃, m₂, m₁]
  · intro i hi
    rw [e₅, h₄ i hi, e₃]

end VG.Proof.Ed25519.X86
