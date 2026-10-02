import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCrypt

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The ciphertext absorbed into
GHASH (`textAbsorb`), then decrypted in place (`crypt`), for any message the
state represents (`streamDecrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- One run of `vg_aes_gcm_stream_decrypt`, for the message the state represents. -/
theorem streamDecrypt_run (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamDecryptX86_64.pre s)
    {iv a c : List Byte} (hA : s.gpr .rcx = BitVec.ofNat 64 a.length) (hT : (s.gpr .r8).toNat = c.length) :
    WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧
      let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      let h := ctxH s.mem (s.gpr .rdi)
      (StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
        let c' := c ++ bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
        StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c' ∧
          bytesAt s'.mem (s.gpr .r9) (stackArg s 0).toNat = (gctr ciph (inc32 (Spec.Gcm.j0 h iv)) c').drop c.length) := by
  have C := CryptCtx.of hp
  have hR := C.rounds
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hW : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  have L := C.lay
  generalize hR' : (s.gpr .rsi).toNat = R at *
  generalize hH : ctxH s.mem Ctx = H
  generalize hciph : ctxCiph s.mem Ctx R = ciph
  refine WP.seq (WP.mono (cryptEntry_ok hCtx hSt hD hSP hW hn C.perm C.ww C.args C.dA (by rw [hR']; exact hR))
    fun s₁ E => ?_)
  have hRo : RoundsAt s₁.mem W R := hR' ▸ E.rounds
  have dCE : ∀ r ∈ [entryR W], (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame E.frame (fun r hr => (dCE r hr).sub_left (Lay.ctxSub (by decide))), ← hH, ctxH_eq]
  have hta : TaIn Ctx St W SP H (s.gpr .rcx) (s.gpr .r8) D n s₁ :=
    ⟨E.env, hH₁, E.alen, E.tlen, E.dat, E.len, (C.data.of_eq E.rd E.wr).ok⟩
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok v L hta hA hT)) fun s₂ ⟨⟨he₂, f₂, hab⟩, hrd₂, hwr₂⟩ => ?_)
  have rd₂ : ∀ d, 176 ≤ d → d + 8 ≤ 512 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_taFrame L h₁ h₂)
      (by decide)
  have q₁ := he₂.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he₂.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have q₃ := he₂.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, h12, hbp, hbx, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.mem (at_ .r15 tlenO)), .alu .and .rbx (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r12 = D ∧ s₃.gpr .rbp = BitVec.ofNat 64 n ∧ s₃.gpr .rbx = BitVec.ofNat 64 (c.length % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧
      s₃.wr = s₂.wr := by
    have hand := and15 (s.gpr .r8)
    rw [imm_eq (by decide), hT] at hand
    refine ⟨_, by xrun [he₂.r15, q₁, q₂, q₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, rd₂ 200 (by decide) (by decide), E.dat]
    · simp [gpr_setReg, rd₂ 208 (by decide) (by decide), E.len]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, rd₂ 192 (by decide) (by decide), E.tlen, hand]
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide) (by decide)) hrd₃ hwr₃
  have hR₃ : RoundsAt s₃.mem W R := ⟨by rw [hm₃, rd₂ 176 (by decide) (by decide)]; exact hRo.1, hRo.2⟩
  generalize hicb : inc32 (Spec.Gcm.j0 H iv) = icb
  have hcr : CrIn Ctx St W SP R icb c.length D n s₃ :=
    ⟨he₃, h12, hbp, hbx, C.data.of_eq (by rw [hrd₃, hrd₂, E.rd]) (by rw [hwr₃, hwr₂, E.wr]), hR₃⟩
  refine WP.seq (WP.mono (crypt_ok v L hcr) fun s₄ co => ?_)
  have dSa : ∀ r ∈ taFrame St W SP, (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  have hsv₂ : SavedAt s₂.mem W s := E.saved.frame f₂ dSa
  have hsv₃ : SavedAt s₃.mem W s := by rw [hm₃]; exact hsv₂
  have hsv₄ : SavedAt s₄.mem W s := hsv₃.frame co.frame (saved_crFrame L (C.data.of_eq E.rd E.wr))
  have hret : s₄.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept co.frame (fun r hr => ?_), hm₃, ret_kept f₂ (fun r hr => ?_), ret_kept E.frame (fun r hr => ?_)]
    · simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact C.rS.sub_right (Lay.stSub (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact C.rD
      · exact C.rS.sub_right (Lay.stSub (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
  refine WP.mono (exit_ok co.env.r15 (by rw [co.env.rsp, hSP]) (covers_left co.env.perm.w) hsv₄ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, fun hsr => ?_⟩
  dsimp only at hsr ⊢
  rw [hicb]
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hsr ⊢
  obtain ⟨hj, habs, hctr⟩ := hsr
  rw [hicb] at hctr ⊢
  have dD : ∀ r ∈ [entryR W], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide))
  have dDa : ∀ r ∈ taFrame St W SP, (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact C.data.ok.st.sub_right (Lay.stSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.data.ok.stk.symm
  have hd₁ : bytesAt s₁.mem D n = bytesAt s.mem D n := bytesAt_frame E.frame dD (by have := C.data.ok.lt; omega)
  have hd₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by
    rw [hm₃, bytesAt_frame f₂ dDa (by have := C.data.ok.lt; omega), hd₁]
  have hc₃ : ciphOf s₃.mem Ctx R = ciph := by
    rw [hm₃, ciph_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.cs.sub_right (Lay.stSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.kc.symm) hR,
      ciph_frame E.frame dCE hR, ← hciph]; rfl
  have hctr₃ : Ctr s₃.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf s₃.mem Ctx R) icb c.length := by
    rw [hc₃, hm₃]
    exact (hctr.congr (blockAt_frame E.frame (st_disj C (d := 48) (k := 16) (by decide)).1)
      (blockAt_frame E.frame (st_disj C (d := 64) (k := 16) (by decide)).1)).congr
      (blockAt_frame f₂ ((st_disj C (d := 48) (k := 16) (by decide)).2.2 (.inr (by decide))))
      (blockAt_frame f₂ ((st_disj C (d := 64) (k := 16) (by decide)).2.2 (.inr (by decide))))
  have habs₁ : Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c) := by
    have hl := Nat.mod_lt (ghashInput a c).length (show 16 > 0 by decide)
    exact habs.congr (blockAt_frame E.frame (st_disj C (d := 16) (k := 16) (by decide)).1)
      (bytesAt_frame E.frame (st_disj C (d := 32) (k := _ % 16) (by omega)).1 (by omega))
  have hab₂ := hab habs₁
  rw [hd₁] at hab₂
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hm, ← hj]
    simpa using (blockAt_frame co.frame ((st_disj C (d := 0) (k := 16) (by decide)).2.1 (by decide))).trans
      ((by rw [hm₃] : blockAt s₃.mem (St + BitVec.ofNat 64 0) = blockAt s₂.mem (St + BitVec.ofNat 64 0)).trans
      ((blockAt_frame f₂ ((st_disj C (d := 0) (k := 16) (by decide)).2.2 (.inl (by decide)))).trans
      (blockAt_frame E.frame (st_disj C (d := 0) (k := 16) (by decide)).1)))
  · rw [hm]
    have hl := Nat.mod_lt (ghashInput a (c ++ bytesAt s.mem D n)).length (show 16 > 0 by decide)
    rw [← hm₃] at hab₂
    exact hab₂.congr (blockAt_frame co.frame ((st_disj C (d := 16) (k := 16) (by decide)).2.1 (by decide)))
      (bytesAt_frame co.frame ((st_disj C (d := 32) (k := _ % 16) (by omega)).2.1 (by omega)) (by omega))
  · rw [hm, List.length_append, length_bytesAt]
    have := co.ctr hctr₃
    rwa [hc₃] at this
  · rw [hm, co.out hctr₃, hc₃, hd₃, Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

/-- `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecrypt_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.streamDecryptX86_64.pre s) :
    WP isa (streamDecrypt v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (streamDecrypt_run v hp (iv := []) (a := List.replicate (s.gpr .rcx).toNat 0)
      (c := List.replicate (s.gpr .r8).toNat 0) (by simp) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (streamDecrypt_run v hp (iv := i.1) hi.1 hi.2) fun _ h => h.2
  exact WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => hq (iv, a, c) ⟨hA, hT⟩ hr⟩

end VG.Proof.AesGcm.X86_64
