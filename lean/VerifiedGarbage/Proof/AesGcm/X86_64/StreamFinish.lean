import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry of `finish` and
`verify` keeps the number of rounds and the lengths in `W` (`finEntry_ok`);
`finish` then writes the tag (`finTag 0`) for any message the state
represents (`streamFinish_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)

/-- The kept public values. -/
abbrev slotsR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 176, 24⟩

/-- After `finEntry`: the registers, the kept values, and what changed. -/
structure FinEntry (s₀ : State) (Ctx St W SP : Addr) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W (s₀.gpr .rsi).toNat
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rcx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .r8
  saved : SavedAt s.mem W s₀
  frame : Frame [savedR W, slotsR W] s₀.mem s.mem

theorem finEntry_ok {s : State} {Ctx St W SP : Addr} (hCtx : s.gpr .rdi = Ctx) (hSt : s.gpr .rdx = St)
    (hW : s.gpr .r9 = W) (hSP : s.gpr .rsp = SP) (hperm : Perm Ctx St W s) (_hww : W.toNat + 2560 ≤ 2 ^ 64)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block finEntry) s (FinEntry s Ctx St W SP) := by
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, hsv₁, f₁⟩ := save_ok s .r9 hW hperm.w
  have w₁ := in_off hperm.w (show 176 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hperm.w (show 184 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hperm.w (show 192 + 8 ≤ 2560 by decide) (by decide)
  rw [← hwr₁] at w₁ w₂ w₃
  obtain ⟨s₂, run₂, h15, h14, h13, hsp, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r9), .mov .r14 (.reg .rdx), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
        .store (at_ .r15 alenO) .rcx, .store (at_ .r15 tlenO) .r8] s₁ = some s₂ ∧
      s₂.gpr .r15 = W ∧ s₂.gpr .r14 = St ∧ s₂.gpr .r13 = Ctx ∧ s₂.gpr .rsp = SP ∧
      s₂.mem = ((s₁.mem.writeW (W + BitVec.ofNat 64 176) (s.gpr .rsi)).writeW (W + BitVec.ofNat 64 184)
        (s.gpr .rcx)).writeW (W + BitVec.ofNat 64 192) (s.gpr .r8) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have h9 : s₁.gpr .r9 = W := by rw [hg₁, hW]
    refine ⟨_, by xrun [h9, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁, hW]
    · simp [gpr_setReg, hg₁, hSt]
    · simp [gpr_setReg, hg₁, hCtx]
    · simp [gpr_setReg, hg₁, hSP]
    · simp [mem_setReg, gpr_setReg, hg₁]
    all_goals rfl
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have s₁₂ := sep 176 184 (by decide) (by decide) (by decide)
  have s₁₃ := sep 176 192 (by decide) (by decide) (by decide)
  have s₂₃ := sep 184 192 (by decide) (by decide) (by decide)
  have f₂ : Frame [slotsR W] s₁.mem s₂.mem := by
    rw [hm₂]
    have c : ∀ d, 176 ≤ d → d + 8 ≤ 200 → (slotsR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  refine ⟨⟨h13, h14, h15, hsp, hperm.of_eq (hrd₂.trans hrd₁) (hwr₂.trans hwr₁)⟩, ⟨?_, hR⟩, ?_, ?_, ?_, ?_⟩
  · rw [hm₂]
    simp (disch := first | decide | assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
    exact BitVec.eq_of_toNat_eq (by simp)
  · rw [hm₂]
    simp (disch := first | decide | assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · rw [hm₂]
    simp (disch := first | decide | assumption) only [Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · refine hsv₁.frame f₂ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega)
  · exact (f₁.mono fun r hr => by simp at hr; subst hr; simp).trans (f₂.mono fun r hr => by simp at hr; subst hr; simp)

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput ghashFrom ghash blocks zeros padLen ofBytes
  toBytes)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)

theorem ghashInput_mod (a c : List Byte) :
    (ghashInput a c).length % 16 = (if c = [] then a.length else c.length) % 16 := by
  by_cases hc : c = []
  · subst hc; rfl
  · rw [Proof.Gcm.ghashInput_of_ne hc]
    simp only [hc, ↓reduceIte]
    simp only [List.length_append, Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega

/-- One run of `vg_aes_gcm_stream_finish`, for the input `x` GHASH has. -/
theorem streamFinish_run (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamFinishX86_64.pre s) {x : List Byte}
    (hx : x.length % 16 = (if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) :
    WP isa (streamFinish v.callees) s fun s' => gprPreserved s s' ∧
      (Absorbed s.mem (s.gpr .rdx + BitVec.ofNat 64 16) (s.gpr .rdx + BitVec.ofNat 64 32) (ctxH s.mem (s.gpr .rdi)) x →
        bytesAt s'.mem (s.gpr .r9) 16 =
          toBytes (ghashFrom (ctxH s.mem (s.gpr .rdi)) (ghash (ctxH s.mem (s.gpr .rdi))
            (blocks (x ++ zeros (padLen x.length)))) [ofBytes (lensBlock (s.gpr .rcx).toNat (s.gpr .r8).toNat)] ^^^
            ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat (blockAt s.mem (s.gpr .rdx)))) := by
  have hp' := hp
  simp only [Proof.AesGcm.streamFinishX86_64, Proof.AesGcm.finPre, Proof.AesGcm.stk, Proof.AesGcm.ret,
    Proof.AesGcm.rounds] at hp'
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, r_s, r_w, k_c, k_s, k_w, wc, ws, ww, hR⟩ := hp'
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : s.gpr .r9 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  have L : Lay Ctx St W SP := Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  have hperm : Perm Ctx St W s := ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  refine WP.seq (WP.mono (finEntry_ok hCtx hSt hW hSP hperm ww hR) fun s₁ he => ?_)
  have dF : ∀ d k, (d + k ≤ 16 ∨ (16 ≤ d ∧ d + k ≤ 80)) → ∀ r ∈ [savedR W, slotsR W],
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (d_sw.sub_left (Lay.stSub (by omega))).sub_right (Lay.wSub (by decide))
    · exact (d_sw.sub_left (Lay.stSub (by omega))).sub_right (Lay.wSub (by decide))
  have dC : ∀ r ∈ [savedR W, slotsR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact d_cw.sub_right (Lay.wSub (by decide))
  have hH : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq, blockAt_frame he.frame fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))]
  refine WP.seq (WP.mono (finTag_ok v L (o := 0) (.inl rfl) he.env he.rounds he.alen he.tlen hx) fun s₂ ⟨he₂, _, f₂, ht⟩ => ?_)
  have hret : s₂.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₂ (fun r hr => ?_), ret_kept he.frame (fun r hr => ?_)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact r_w.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact r_s.sub_right (Region.sub_prefix (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact r_w.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
  refine WP.mono (exit_ok he₂.r15 (by rw [he₂.rsp, hSP]) (covers_left he₂.perm.w)
    (he.saved.frame f₂ (saved_tagFrame L (.inl rfl))) (by rw [hSP, hret])) fun s' ⟨hg, hm, _⟩ => ⟨hg, fun ha => ?_⟩
  have ha₁ : Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s₁.mem (Ctx + BitVec.ofNat 64 240)) x := by
    rw [hH]
    exact ha.congr (blockAt_frame he.frame (dF 16 16 (.inr ⟨by decide, by decide⟩)))
      (bytesAt_frame he.frame (dF 32 (x.length % 16) (.inr ⟨by decide, by omega⟩)) (by omega))
  have hc : ciphOf s₁.mem Ctx (s.gpr .rsi).toNat = ctxCiph s.mem Ctx (s.gpr .rsi).toNat :=
    ciph_frame he.frame dC hR
  have hJ : blockAt s₁.mem St = blockAt s.mem St := by
    simpa using blockAt_frame he.frame (dF 0 16 (.inl (by decide)))
  rw [hm, show W = W + BitVec.ofNat 64 0 by simp, ht ha₁, hc, hJ, hH]

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr ctxH ctxCiph ghashInput)

theorem toNat_eq_zero {x : BitVec 64} : x = 0 ↔ x.toNat = 0 :=
  ⟨fun h => by subst h; rfl, fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩

/-- The length GHASH has buffered, from `aad_len` and `text_len`. -/
theorem ghashInput_lens {a c : List Byte} {aL tL : BitVec 64} (ha : aL = BitVec.ofNat 64 a.length)
    (hc : tL.toNat = c.length) :
    (ghashInput a c).length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16 := by
  rw [ghashInput_mod]
  by_cases h : c = []
  · subst h
    have : tL = 0 := toNat_eq_zero.mpr hc
    simp only [this, ↓reduceIte, ha, toNat_mod16]
  · have : tL ≠ 0 := fun e => h (List.eq_nil_of_length_eq_zero (by rw [← hc, toNat_eq_zero.mp e]))
    simp only [h, this, ↓reduceIte, hc]

/-- `vg_aes_gcm_stream_finish`. -/
theorem streamFinish_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamFinishX86_64.pre s) :
    WP isa (streamFinish v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamFinishX86_64.post s s' := by
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (streamFinish_run v hp (x := List.replicate
      ((if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) 0) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (streamFinish_run v hp (ghashInput_lens hi.1 hi.2)) fun _ h => h.2
  refine WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit] at hr
  obtain ⟨hj, ha, -⟩ := hr
  rw [hq (iv, a, c) ⟨hA, hT⟩ ha, Proof.Gcm.fullTag_eq, hj, hA, hT, BitVec.toNat_ofNat, lensBlock_mod_left]
  rfl

end VG.Proof.AesGcm.X86_64
