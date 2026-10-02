import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish

/-!
# AES-GCM on x86-64: text into GHASH (`textAbsorb`)

Untrusted: everything here is checked by Lean. `textAbsorb` absorbs the
`len` bytes at `data` (as kept in `W`) as ciphertext: the additional data
padded first if there is no text yet (`firstFlush`), as `ghashInput`
requires (`textAbsorb_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The regions `textAbsorb` writes. -/
abbrev taFrame (St W SP : Addr) : List Region :=
  [⟨St + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8]

/-- Before `textAbsorb`: the lengths, the data and its length kept in `W`. -/
structure TaIn (Ctx St W SP : Addr) (H : Block) (aL tL : BitVec 64) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  data : DataOk St W SP s D n

theorem tFrame_taFrame {St W SP : Addr} {m m' : Mem} (h : Frame (tFrame St W SP 16) m m') :
    Frame (taFrame St W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨St + BitVec.ofNat 64 16, 32⟩, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 96, 16⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

theorem absFrame_taFrame {St W SP : Addr} {m m' : Mem} (h : Frame (absFrame St W SP 16) m m') :
    Frame (taFrame St W SP) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨St + BitVec.ofNat 64 16, 32⟩, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨⟨St + BitVec.ofNat 64 16, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
  · exact ⟨below SP 8, by simp, fun _ h => h⟩

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- What `textAbsorb` keeps: the values in `W` outside what it writes. -/
theorem kept_taFrame {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 512) :
    ∀ r ∈ taFrame St W SP, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

/-- `textAbsorb`, for additional data `a` and ciphertext so far `c` of the
kept lengths. -/
theorem textAbsorb_ok {H : Block} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s : State}
    (h : TaIn Ctx St W SP H aL tL D n s) {a c : List Byte} (hA : aL = BitVec.ofNat 64 a.length)
    (hT : tL.toNat = c.length) :
    WP isa (textAbsorb v.callees) s fun s' => Env Ctx St W SP s' ∧ Frame (taFrame St W SP) s.mem s'.mem ∧
      (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
        Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c ++ bytesAt s.mem D n))) := by
  have he := h.env
  have hlt := h.data.lt
  have r₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hbp₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rbp (.mem (at_ .r15 lenO)),
      .alu .test .rbp (.reg .rbp)] s = some s₁ ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.zf = some (decide (n = 0)) ∧
      (∀ r, r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.len]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, h.len]; rw [and_self_beq hlt]
    · intro r a; simp [gpr_setReg, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact Frame.refl _ _, fun ha => by
      rw [hm₁]; simpa [bytesAt] using ha⟩
  · have h0 : n ≠ 0 := by simpa using hf
    have r₂ := he₁.perm.wR (show 192 + 8 ≤ 2560 by decide)
    have htl₁ : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = tL := by rw [hm₁]; exact h.tlen
    obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
        .alu .test .rax (.reg .rax)] s₁ = some s₂ ∧ s₂.zf = some (decide (tL.toNat = 0)) ∧
        (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [he₁.r15, r₂], ?_, ?_, ?_⟩
      · simp only [zf_arithFlags, gpr_setReg, ite_true, htl₁]
        have := and_self_beq tL.isLt
        rw [BitVec.ofNat_toNat] at this
        exact congrArg some this
      · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
    have hm₂' : s₂.mem = s.mem := hm₂.trans hm₁
    -- The additional data padded first, if there is no text yet.
    refine WP.seq (WP.mono (WP.with_rdwr (Q := fun (s₃ : State) => Env Ctx St W SP s₃ ∧ Frame (tFrame St W SP 16) s.mem s₃.mem ∧
        (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) →
          Absorbed s₃.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
            (if c = [] then a ++ zeros (padLen a.length) else ghashInput a c)))
      (WP.ite (decide (tL.toNat = 0)) (eval_e hz₂) (fun ht => ?_) (fun hf => ?_))) fun s₃ h₃ => ?_)
    · have hc : c = [] := List.eq_nil_of_length_eq_zero (by rw [← hT]; simpa using ht)
      subst hc
      have r₃ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
      obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
          .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (a.length % 16) ∧
          (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
        have hand := and15 aL
        rw [imm_eq (by decide), hA, toNat_mod16] at hand
        refine ⟨_, by xrun [he₂.r15, r₃], ?_, ?_, ?_⟩
        · simp only [gpr_setReg, gpr_arithFlags, ite_true, hm₂', h.alen, hand, hA]
        · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
        all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
      refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
      have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
      have hm₃' : s₃.mem = s.mem := hm₃.trans hm₂'
      refine WP.mono (flush_ok v L (yo := 16) (.inr rfl) (H := H) (x := a) ⟨he₃, by rw [hm₃', h.hH]⟩ hbx₃)
        fun s₄ hf => ⟨hf.env, hm₃' ▸ hf.frame, fun ha => ?_⟩
      simp only [↓reduceIte]
      exact hf.abs (by rw [hm₃']; exact ha)
    · have hc : c ≠ [] := fun e => by subst e; simp_all
      exact WP.block_nil ⟨he₂, by rw [hm₂']; exact Frame.refl _ _, fun ha => by simpa [hc, hm₂'] using ha⟩
    obtain ⟨⟨he₃, f₃, hab₃⟩, hrd₃', hwr₃'⟩ := h₃
    have g₃ := tFrame_taFrame f₃
    have rd₃ : ∀ d, 176 ≤ d → d + 8 ≤ 512 → s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
      fun d h₁ h₂ => g₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_taFrame L h₁ h₂)
        (by decide)
    generalize hy : (if c = [] then a ++ zeros (padLen a.length) else ghashInput a c) = y at hab₃
    have hyl : y.length % 16 = c.length % 16 := by
      rw [← hy]
      split
      · next hc => subst hc; simp only [List.length_append, Proof.Gcm.length_zeros, List.length_nil]
                   exact Proof.Gcm.length_pad_mod _
      · next hc => rw [ghashInput_mod]; simp [hc]
    have q₁ := he₃.perm.wR (show 200 + 8 ≤ 2560 by decide)
    have q₂ := he₃.perm.wR (show 208 + 8 ≤ 2560 by decide)
    have q₃ := he₃.perm.wR (show 192 + 8 ≤ 2560 by decide)
    obtain ⟨s₄, run₄, h12, hbp, hbx, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
        .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.mem (at_ .r15 tlenO)), .alu .and .rbx (imm 15)] s₃ = some s₄ ∧
        s₄.gpr .r12 = D ∧ s₄.gpr .rbp = BitVec.ofNat 64 n ∧ s₄.gpr .rbx = BitVec.ofNat 64 (y.length % 16) ∧
        (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧
        s₄.wr = s₃.wr := by
      have hand := and15 tL
      rw [imm_eq (by decide), hT, ← hyl] at hand
      refine ⟨_, by xrun [he₃.r15, q₁, q₂, q₃], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, rd₃ 200 (by decide) (by decide), h.dat]
      · simp [gpr_setReg, rd₃ 208 (by decide) (by decide), h.len]
      · simp only [gpr_setReg, gpr_arithFlags, ite_true, rd₃ 192 (by decide) (by decide), h.tlen, hand]
      · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    have he₄ : Env Ctx St W SP s₄ := he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)) hrd₄ hwr₄
    have dD : ∀ r ∈ tFrame St W SP 16, (⟨D, n⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.data.st.sub_right (Lay.stSub (by decide))
      · exact h.data.w.sub_right (Lay.wSub (by decide))
      · exact h.data.w.sub_right (Lay.wSub (by decide))
      · exact h.data.stk.symm
    have hd₄ : bytesAt s₄.mem D n = bytesAt s.mem D n := by rw [hm₄]; exact bytesAt_frame f₃ dD (by omega)
    have hH₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [hm₄, blockAt_frame f₃ (ctx_tFrame L (.inr rfl)), h.hH]
    have hai : AbsIn Ctx St W SP 16 H y D n s₄ := ⟨he₄, h12, hbp, hbx,
      h.data.of_eq (by rw [hrd₄, hrd₃', hrd₂, hrd₁]) (by rw [hwr₄, hwr₃', hwr₂, hwr₁]), hH₄⟩
    refine WP.mono (absorb_ok v L (yo := 16) (.inr rfl) hai) fun s₅ ho => ⟨ho.env, ?_, fun ha => ?_⟩
    · have := absFrame_taFrame ho.frame
      rw [hm₄] at this
      exact (tFrame_taFrame f₃).trans this
    · have hd : bytesAt s.mem D n ≠ [] := fun e => h0 (by rw [← length_bytesAt s.mem D n, e]; rfl)
      rw [Proof.Gcm.ghashInput_append _ _ _ hd, hy, ← hd₄]
      exact ho.abs (by rw [hm₄]; exact hab₃ ha)

end

end VG.Proof.AesGcm.X86_64
