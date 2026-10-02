import VerifiedGarbage.Proof.AesGcm.AArch64.FinTag
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCrypt

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and keeps the lengths in `x26` and `x27` (`finEntry_ok`);
`finBody 0` writes the tag to `W`, for any message of those lengths
(`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes ctxCiph ctxH)
open VG.Proof.Gcm (Absorbed lensBlock padded)

/-- After the entry: the lengths. -/
theorem finEntry_ok {s : State} {Ctx St W : Addr} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x2 = St)
    (hW : s.gpr .x5 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block finEntry) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s'.gpr .x26 = s.gpr .x3 ∧ s'.gpr .x27 = s.gpr .x4 ∧
      s'.gpr .x6 = s.gpr .x6 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s .x5 hW hperm.w
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x22₂, x26₂, x27₂, x6₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x5, mov .x20 .x2, mov .x21 .x0, mov .x22 .x1, mov .x26 .x3, mov .x27 .x4] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s₂.gpr .x26 = s.gpr .x3 ∧ s₂.gpr .x27 = s.gpr .x4 ∧
      s₂.gpr .x6 = s.gpr .x6 ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> simp [gpr_write, g₁, hW, hSt, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x22₂, x26₂, x27₂, x6₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- What `finPre` gives. -/
theorem lay_of_fin {s : State} (hs : finPre s) :
    Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x5) ∧ Perm (s.gpr .x0) (s.gpr .x2) (s.gpr .x5) s ∧
      rounds (s.gpr .x1) := by
  simp only [finPre] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dsw, wc, ws, ww, hR⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw,
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩, hR⟩

/-- What the entry's writes keep. -/
theorem fin_inv {s : State} (hs : finPre s) {m : Mem} (hf : Frame [savedR (s.gpr .x5)] s.mem m) {x : List Byte} :
    ciphOf m (s.gpr .x0) (s.gpr .x1).toNat = ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat ∧
      blockAt m (s.gpr .x2) = blockAt s.mem (s.gpr .x2) ∧
      blockAt m (s.gpr .x0 + BitVec.ofNat 64 240) = ctxH s.mem (s.gpr .x0) ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) x →
        Absorbed m (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) x) := by
  obtain ⟨L, -, hR⟩ := lay_of_fin hs
  have sW : Region.Sub (savedR (s.gpr .x5)) ⟨s.gpr .x5, 2560⟩ := Lay.wSub (by decide)
  refine ⟨ciph_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right sW) hR,
    blockAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact st0_saved L),
    blockAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right sW),
    fun ha => Absorbed.frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩) ha⟩

/-- One run of `stream_finish`, for a message `a`, `c` of those lengths. -/
theorem fin_run (v : GcmImpl) {s : State} (hs : streamFinishAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x3 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x4 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamFinish v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        bytesAt s'.mem (s.gpr .x5) 16 =
          toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2)))) := by
  have hs' : finPre s := hs
  obtain ⟨L, perm, hR⟩ := lay_of_fin hs'
  refine WP.seq (WP.mono (finEntry_ok rfl rfl rfl perm)
    fun s₁ ⟨he₁, hk₁, x22₁, x26₁, x27₁, _, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR (s.gpr .x5)] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  obtain ⟨hc₁, hj₁, hH₁, hA₁⟩ := fin_inv hs' fsv (x := ghashInput a c)
  refine WP.seq (WP.mono (finBody_ok L v (.inl rfl) (a := a) (c := c) he₁ hk₁ x22₁ hR (by rw [x26₁, h3]) (by rw [x27₁, h4]) hc hH₁)
    fun s₂ ⟨he₂, hk₂, f₂, out₂⟩ => ?_)
  have hsv : SavedAt s₂.mem (s.gpr .x5) s := by
    have := savedAt_save s.mem (s.gpr .x5) s
    rw [← m₁] at this
    exact this.frame f₂ (saved_finFrame L (.inl rfl))
  refine WP.mono (exit_ok he₂.x19 he₂.sp (covers_left he₂.perm.w) hsv) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, fun ha => ?_⟩
  rw [hm, ← hc₁, ← hj₁]
  have := out₂ (hA₁ ha)
  rw [add_ofNat_zero] at this
  exact this

theorem streamFinish_wp (v : GcmImpl) {s : State} (hs : streamFinishAArch64.pre s) :
    WP isa (streamFinish v.callees) s fun s' => GprAbi s s' ∧ streamFinishAArch64.post s s' := by
  have h3 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x4 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x4).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x4).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' => bytesAt s'.mem (s.gpr .x5) 16 = Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2)
    (fin_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x4).toNat = c.length := hc
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x4 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (fin_run v hs hl h4c (hc ▸ (s.gpr .x4).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  show _ = Spec.Gcm.fullTag ciph h iv a c
  rw [hout habs, Proof.Gcm.fullTag_eq, hj]
  rfl

end VG.Proof.AesGcm.AArch64
