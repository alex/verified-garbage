import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts

/-!
# AES-GCM on x86-64: `oneUndo`

Untrusted: everything here is checked by Lean. When the tag is wrong, `open`
encrypts again the whole blocks `oneBlocks` decrypted, with `vg_aes_ctr32`
from the counter block at the state's start (`oneUndo_ok`), which `tag` left
there.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32)

/-- The blocks of `oneUndo`. -/
abbrev undoB1 : List Instr :=
  [.mov .rax (.mem (at_ .r15 tlenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15),
    .alu .sub .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 dataO)), .alu .sub .rcx (.reg .rax),
    .shift .shr .rax 4, .mov .r8 (.reg .rax), .alu .test .rax (.reg .rax)]
abbrev undoB2 : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14)] : List Instr) ++
    ptr .r9 .r15 scrO

theorem oneUndo_eq (c : Callees) : oneUndo c = .seq (.block undoB1) (.ite .e (.block [])
    (.seq (.block undoB2) (.call c.ctr.name c.ctr.code))) := rfl

/-- What `oneUndo` writes: the counter block, the whole blocks, the working
space and the stack. -/
abbrev undoFrame (W SP D : Addr) (q : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨D, 16 * q⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, below SP 8]

section
variable {Ctx W SP : Addr}

/-- The data's start and its number of whole blocks. -/
theorem undo1_ok {D : Addr} {n : Nat} (hn : n < 2 ^ 64) {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16))) :
    WP isa (.block undoB1) s fun s₁ => s₁.gpr .rcx = D ∧ s₁.gpr .r8 = BitVec.ofNat 64 (n / 16) ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have e15 := and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hn]; congr 1; omega
  have ed : D + BitVec.ofNat 64 (16 * (n / 16)) - BitVec.ofNat 64 (16 * (n / 16)) = D := BitVec.add_sub_cancel _ _
  have h4 := shr4 (16 * (n / 16)) (by omega)
  rw [show 16 * (n / 16) / 16 = n / 16 by omega] at h4
  have hz := and_self_beq (show n / 16 < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, htl, hdat, e15, esub, ed, h4], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, ed]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, h4, hz]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

variable (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneUndo`: counter mode over the whole blocks of the data, from the
counter block at the state's start. -/
theorem oneUndo_ok (c : Callees) (v : Proof.Aes.X86_64.Ctr32Impl) (hc : c.ctr = ⟨v.callee.name, v.callee.code⟩)
    {R : Nat} {D : Addr} {n : Nat} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16)))
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa (oneUndo c) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (undoFrame W SP D (n / 16)) s.mem s'.mem ∧
      blocksAt s'.mem D (n / 16) = ctr32 (ciphOf s.mem Ctx R) (blockAt s.mem (W + BitVec.ofNat 64 16))
        (blocksAt s.mem D (n / 16)) ∧
      blockAt s'.mem (W + BitVec.ofNat 64 16) =
        Nat.repeat Spec.Gcm.inc32 (n / 16) (blockAt s.mem (W + BitVec.ofNat 64 16)) := by
  have hn := hd.ok.lt
  rw [oneUndo_eq]
  refine WP.seq (WP.mono (undo1_ok hn he htl hdat) fun s₁ ⟨hcx, h8, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) rd₁ wr₁
  refine WP.ite (decide (n / 16 = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.block_nil ⟨he₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_⟩
    · rw [hz, m₁]; rfl
    · rw [hz, m₁]; rfl
  · simp only [decide_eq_false_iff_not] at hz
    have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
    have r₃ := he₁.perm.wR (show 176 + 8 ≤ 2560 by decide)
    have hR₁ : s₁.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 R := by rw [m₁]; exact hR.1
    obtain ⟨s₂, run₂, hdi, hsi, hdx, h9, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa undoB2 s₁ = some s₂ ∧
        s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 16 ∧
        s₂.gpr .r9 = W + BitVec.ofNat 64 512 ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .r9 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
        s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [h13, h14, h15, r₃, hR₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, gpr_arithFlags, h13]
      · simp [gpr_setReg, gpr_arithFlags, h15, hR₁]
      · simp [gpr_setReg, gpr_arithFlags, h14]
      · simp [gpr_setReg, gpr_arithFlags, h15, imm_eq, scrO]
      · intro r a b c d; simp [gpr_setReg, gpr_arithFlags, a, b, c, d]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
    have hk := he₂.rsp
    have hq : 16 * (n / 16) ≤ n := by omega
    have hdq := (hd.of_eq (hrd₂.trans rd₁) (hwr₂.trans wr₁)).take hq
    have hS : (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩ := by
      simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
    have kc : (⟨Ctx, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 16, 16⟩ := by
      simpa using (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (d := 0) (n := 16) (by decide))
    have cd : (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint ⟨D, 16 * (n / 16)⟩ := by
      have := hdq.ok.st.sub_right (Lay.stSub (St := W + BitVec.ofNat 64 16) (d := 0) (n := 16) (by decide))
      simpa using this.symm
    have hcall : CtrCall s₂ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) := by
      refine ⟨hdi, hsi, hdx, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hcx,
        by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide)]; exact h8, h9, hR.2,
        by have := hd.ok.wrap; omega, kc, hdq.ctx.sub_left (Region.sub_prefix (show 240 ≤ 256 by decide)),
        (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
        cd, hS, hdq.ok.w.sub_right (Lay.wSub (by decide)), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
      · rw [hk]; simpa using L.stk_st (a := 0) (n := 16) (by decide)
      · rw [hk]; exact hdq.ok.stk
      · rw [hk]; exact L.stk_w (by decide)
      · refine covers_cons ?_ (covers_cons ?_ (covers_cons hdq.ok.rd (covers_left (he₂.perm.wC (by decide)))))
        · exact fun a m' ⟨r, hr, hc'⟩ => by
            simp only [List.mem_singleton] at hr; subst hr
            exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
        · simpa using covers_left (he₂.perm.stC (d := 0) (n := 16) (by decide))
      · exact covers_cons (by simpa using he₂.perm.stC (d := 0) (n := 16) (by decide))
          (covers_cons hdq.wr (he₂.perm.wC (by decide)))
    rw [hc]
    refine WP.mono (ctr_call v hcall) fun s₃ g => ?_
    refine ⟨he₂.of_saved g.saved g.rd g.wr, g.rd.trans (hrd₂.trans rd₁), g.wr.trans (hwr₂.trans wr₁), ?_, ?_, ?_⟩
    · rw [← m₁, ← hm₂, ← hk]; exact g.frame
    · rw [g.out, hm₂, m₁]
    · rw [g.ctr, hm₂, m₁]
end

theorem undo_B {W D SP : Addr} {n : Nat} {m m' : Mem} (h : Frame (undoFrame W SP D (n / 16)) m m') :
    Frame (oneFrameB W D SP n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

end VG.Proof.AesGcm.X86_64
