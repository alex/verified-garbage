import VerifiedGarbage.Proof.AesGcm.AArch64.Fn

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `j0`'s arguments (`siEntry_ok`); `j0` writes `J₀`, a
zero accumulator and the first counter block, which is a state for the
nonce, no additional data and no text.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)

theorem covers_mem {r : Region} {rd wr : List Region} (h : r ∈ rd ++ wr) : Covers [r] (rd ++ wr) :=
  covers_of_mem h

/-- After the entry: `j0`'s arguments. -/
theorem siEntry_ok {s : State} {Ctx Np St W : Addr} {n : Nat} (hCtx : s.gpr .x0 = Ctx) (hNp : s.gpr .x1 = Np)
    (hn : (s.gpr .x2).toNat = n) (hSt : s.gpr .x3 = St) (hW : s.gpr .x4 = W)
    (hperm : Perm Ctx St W s) :
    WP isa (.block siEntry) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x23 = Np ∧ s'.gpr .x24 = BitVec.ofNat 64 n ∧ s'.gpr .x26 = BitVec.ofNat 64 n ∧
      s'.gpr .x27 = 0 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x4 hW hperm.w
  have hn' : s.gpr .x2 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x23₂, x24₂, x26₂, x27₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x4, mov .x20 .x3, mov .x21 .x0, mov .x23 .x1, mov .x24 .x2, mov .x26 .x2, imm .x27 0] s₁ =
        some s₂ ∧ s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x23 = Np ∧
      s₂.gpr .x24 = BitVec.ofNat 64 n ∧ s₂.gpr .x26 = BitVec.ofNat 64 n ∧ s₂.gpr .x27 = 0 ∧
      s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> simp [gpr_write, g₁, hCtx, hNp, hn', hSt, hW]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x23₂, x24₂, x26₂, x27₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem streamInit_wp (v : GcmImpl) {s : State} (hs : streamInitAArch64.pre s) :
    WP isa (streamInit v.callees) s fun s' => GprAbi s s' ∧ streamInitAArch64.post s s' := by
  simp only [streamInitAArch64] at hs ⊢
  obtain ⟨hrd, hwr, dcs, dcw, dns, dnw, dsw, wc, wn, ws, ww⟩ := hs
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hNp : s.gpr .x1 = Np at *
  generalize hn : (s.gpr .x2).toNat = n at *
  generalize hSt : s.gpr .x3 = St at *
  generalize hW : s.gpr .x4 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have perm : Perm Ctx St W s :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .x2).isLt
  refine WP.seq (WP.mono (siEntry_ok hCtx hNp hn hSt hW perm)
    fun s₁ ⟨he₁, hk₁, x23₁, x24₁, x26₁, x27₁, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR W] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Lay.wSub (by decide)
  have hiv : bytesAt s₁.mem Np n = bytesAt s.mem Np n :=
    bytesAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnw.sub_right sW) (by omega)
  have hH : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame fsv (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (dcw.sub_left (Lay.ctxSub (by decide))).sub_right sW)
  have hJ : J0In Ctx St W s.sp s₁.gpr (Spec.Gcm.ctxH s.mem Ctx) Np n s₁ :=
    ⟨he₁, hk₁, x23₁, x24₁, x26₁, x27₁,
      ⟨covers_mem (by rw [rd₁, wr₁, hrd]; simp), hlt, wn, dns, dnw⟩, hH⟩
  refine WP.seq (WP.mono (j0_ok L v hJ) fun s₂ h₂ => ?_)
  have hsv : SavedAt s₂.mem W s := by
    have := savedAt_save s.mem W s
    rw [← m₁] at this
    exact this.frame h₂.frame (saved_j0Frame L)
  refine WP.mono (exit_ok h₂.env.x19 h₂.env.sp (covers_left h₂.env.perm.w) hsv) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, fun ciph => ?_⟩
  rw [hm, hiv] at *
  refine Proof.Gcm.streamRepr_iff.mpr ⟨h₂.j0, Proof.Gcm.absorbed_nil _ h₂.y, Proof.Gcm.ctr_zero _ _ _ _ h₂.cb⟩

end VG.Proof.AesGcm.AArch64
