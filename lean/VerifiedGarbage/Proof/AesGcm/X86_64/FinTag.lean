import VerifiedGarbage.Proof.AesGcm.X86_64.Fn

/-!
# AES-GCM on x86-64: the tag of a streaming state (`finTag o`)

Untrusted: everything here is checked by Lean. `finTag o` pads the buffered
bytes (of the additional data if there is no text, of the text if there is)
and writes the tag to `W + o`, from the lengths kept at `W + 184` and
`W + 192` (`finTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes toBytes)
open VG.Proof.Gcm (Absorbed lensBlock)

theorem lensBlock_mod (a c : Nat) : lensBlock (a % 2 ^ 64) (c % 2 ^ 64) = lensBlock a c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a), ← Proof.Gcm.be64_mod (8 * (c % 2 ^ 64)),
    ← Proof.Gcm.be64_mod (8 * c)]
  congr 2 <;> omega

theorem lensBlock_mod_left (a c : Nat) : lensBlock (a % 2 ^ 64) c = lensBlock a c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a)]
  congr 2; omega

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `finTag o`, for buffered input `x` (of the length the lengths give modulo 16). -/
theorem finTag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env Ctx St W SP s)
    (hR : RoundsAt s.mem W R) {aL tL : BitVec 64} (hA : s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL)
    (hT : s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL) {x : List Byte}
    (hx : x.length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16) :
    WP isa (finTag v.callees o) s fun s' => Env Ctx St W SP s' ∧ RoundsAt s'.mem W R ∧
      Frame (tagFrame St W SP o) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) x →
        bytesAt s'.mem (W + BitVec.ofNat 64 o) 16 =
          toBytes (ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
            (ghash (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blocks (x ++ zeros (padLen x.length))))
            [ofBytes (lensBlock aL.toNat tL.toNat)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem St))) := by
  have h15 := he.r15
  have r₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 184 + 8 ≤ 2560 by decide)
  generalize hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  obtain ⟨s₁, run₁, hbx₁, hax₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rbx (.mem (at_ .r15 tlenO)), .mov .rax (.mem (at_ .r15 alenO)), .alu .test .rbx (.reg .rbx)] s =
        some s₁ ∧
      s₁.gpr .rbx = tL ∧ s₁.gpr .rax = aL ∧ s₁.zf = some (decide (tL.toNat = 0)) ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hT]
    · simp [gpr_setReg, hA]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hT]
      have := and_self_beq tL.isLt
      rw [BitVec.ofNat_toNat] at this
      exact congrArg some this
    · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  -- `rbx`: the length of the buffered input, modulo 16.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => Env Ctx St W SP s₂ ∧ s₂.gpr .rbx = (if tL = 0 then aL else tL) ∧
      s₂.mem = s.mem) (WP.ite (decide (tL.toNat = 0)) (eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)) fun s₂ h₂ => ?_)
  · have h0 : tL = 0 := by
      have : tL.toNat = 0 := by simpa using ht
      exact BitVec.eq_of_toNat_eq (by simpa using this)
    refine WP.run (Q := fun s₂ => s₂ = s₁.setReg .rbx (s₁.gpr .rax)) ⟨_, by xrun [], rfl⟩ fun s₂ e => ?_
    subst e
    exact ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl,
      by simp [gpr_setReg, hax₁, h0], by rw [mem_setReg, hm₁]⟩
  · have h0 : tL ≠ 0 := fun e => by subst e; simp at hf
    exact WP.block_nil ⟨he₁, by simp only [hbx₁, h0, ↓reduceIte], hm₁⟩
  obtain ⟨he₂, hbx₂, hm₂⟩ := h₂
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.alu .and .rbx (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .rbx = BitVec.ofNat 64 (x.length % 16) ∧ (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have hand := and15 (if tL = 0 then aL else tL)
    rw [imm_eq (by decide)] at hand
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hbx₂, hand, hx]
      split <;> rfl
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hm₃' : s₃.mem = s.mem := hm₃.trans hm₂
  refine WP.seq (WP.mono (flush_ok v L (yo := 16) (.inr rfl) (H := H) ⟨he₃, by rw [hm₃', hH]⟩ hbx₃) fun s₄ hf => ?_)
  rw [hm₃'] at hf
  have he₄ := hf.env
  have dT : ∀ d, 176 ≤ d → d + 8 ≤ 512 → ∀ r ∈ tFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.stk_w (by omega)).symm
  have hA₄ : s₄.mem.readW (W + BitVec.ofNat 64 184) 64 = aL := by
    rw [hf.frame.readW (r := ⟨W + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _) (dT 184 (by decide) (by decide))
      (by decide), hA]
  have hT₄ : s₄.mem.readW (W + BitVec.ofNat 64 192) 64 = tL := by
    rw [hf.frame.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (dT 192 (by decide) (by decide))
      (by decide), hT]
  have r₃ := he₄.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have r₄ := he₄.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₅, run₅, hbx₅, hbp₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ s₅, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))] s₄ = some s₅ ∧
      s₅.gpr .rbx = aL ∧ s₅.gpr .rbp = tL ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₅.gpr r = s₄.gpr r) ∧
      s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by xrun [he₄.r15, r₃, r₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hA₄]
    · simp [gpr_setReg, hT₄]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ : Env Ctx St W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide)) hrd₅ hwr₅
  have f₅ : Frame (tFrame St W SP 16) s.mem s₅.mem := hm₅ ▸ hf.frame
  have hR₅ : RoundsAt s₅.mem W R := rounds_frame f₅ (fun r hr => dT 176 (by decide) (by decide) r hr) hR
  have hJ₅ : blockAt s₅.mem St = blockAt s.mem St := blockAt_frame f₅ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  have hc₅ : ciphOf s₅.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame f₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm) hR.2
  refine WP.mono (tag_ok v L ho he₅ (by rw [hm₅, hf.hH]) hR₅ hJ₅) fun s₆ ht => ?_
  refine ⟨ht.env, ht.rounds, ?_, fun ha => ?_⟩
  · refine (f₅.sub fun r hr => ?_).trans ht.frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base St (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [ht.out, hc₅, hbx₅, hbp₅]
    have hw := (hf.abs ha).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [hm₅, hw]

end

end VG.Proof.AesGcm.X86_64
