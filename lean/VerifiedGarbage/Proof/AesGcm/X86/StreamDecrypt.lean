import VerifiedGarbage.Proof.AesGcm.X86.StreamEncrypt

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry, the ciphertext
absorbed (`textAbsorb`), the text decrypted (`crypt`) and the exit, as one
`Pc` (`streamDecrypt_pc`): correct (`streamDecrypt_correct`) and constant
time (`streamDecrypt_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph gctr inc32 j0)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem streamDecrypt_eq : streamDecrypt = .seq (entry 9 (([.mov .esi (argOp 2)] : List Instr) ++
    (crKeeps.flatMap (fun p => keep p.1 p.2) ++ [])))
    (.seq textAbsorb (.seq (.block setText) (.seq crypt (.block restore)))) := rfl

theorem streamDecrypt_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamCryptPre s₀ ∧ pubOf 10 s₀ = p ∧ s = s₀) streamDecrypt
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamDecryptX86.post s₀ s') := by
  by_cases hex : ∃ s₀, streamCryptPre s₀ ∧ pubOf 10 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have hc := crPure_of hz hzp
  have L := hc.lay
  rw [streamDecrypt_eq]
  refine Pc.seq (crEntry_pc p) ?_
  refine Pc.seq (Pc.lift (textAbsorb_pc L (D := p.2 7) (n := (p.2 8).toNat) (al := p.2 3) (ah := p.2 4)
    (xl := p.2 5) (xh := p.2 6)) (fun _ s => s.mem) fun s₀ s h =>
      ⟨⟨h.env, h.ta, (p.2 8).isLt, (cr_dataW hc h.pre h.pub h.wr).ok⟩, rfl⟩) ?_
  -- The text, as `crypt` takes it.
  refine Pc.seq (Q := fun s₀ s₃ => ∃ s₂, (∃ s₁, CEnt p s₀ s₁ ∧
      TaOut (p.2 0) (p.2 2) (p.2 9) p.1 28 (p.2 7) (p.2 8).toNat (p.2 3) (p.2 4) (p.2 5) (p.2 6) s₁.mem s₂ ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr) ∧
      CrIn (p.2 0) (p.2 2) (p.2 9) p.1 28 (p.2 1).toNat (p.2 7) (p.2 8).toNat (p.2 6 ++ p.2 5).toNat s₃ ∧
      Frame [pslotR (p.2 9)] s₂.mem s₃.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr)
    (Pc.taint [.ebp] (fun s₀ s₂ h => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s₁, h₁, ta, rd₂, wr₂⟩ := h
    have sl := h₁.ta.frame ta.frame (kept_taFrame L)
    obtain ⟨s₃, run, d, n, b, fr, bp, si, sp, rd, wr⟩ := setText_ok L ta.env sl
    refine WP.of_runBlock ⟨s₃, run, s₂, ⟨s₁, h₁, ta, rd₂, wr₂⟩, ?_, fr, rd, wr⟩
    have kP : ∀ r ∈ [pslotR (p.2 9)], (keptR (p.2 9)).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    refine ⟨ta.env.keep bp si sp rd wr (slot_frame fr fun r hr => (kP r hr).sub_left (Offset.sub _ (by decide)
      (by decide))), d, n, by rw [b, append_toNat32]; congr 1; omega, (p.2 8).isLt,
      cr_dataW hc h₁.pre h₁.pub (by rw [wr, wr₂, h₁.wr]),
      rounds_frame fr kP (rounds_frame ta.frame (kept_taFrame L) h₁.rounds)⟩
  refine Pc.seq (Pc.lift (Pc.forall fun icb => crypt_pc L rfl (R := (p.2 1).toNat) (icb := icb) (D := p.2 7)
    (n := (p.2 8).toNat) (P := (p.2 6 ++ p.2 5).toNat)) (fun _ s => s.mem) fun s₀ s ⟨_, _, hin, _⟩ => ⟨hin, rfl⟩) ?_
  refine Pc.taint [.ebp] (fun s₀ s₄ ⟨s₃, ⟨s₂, ⟨s₁, h₁, ta, rd₂, wr₂⟩, hin, fr, rd₃, wr₃⟩, co, rd₄, wr₄⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h₁ default).env.ebp, (h₂ default).env.ebp])
    (by taint_decide)
  have hf : Frame (pslotR (p.2 9) :: crFrame (p.2 2) (p.2 9) p.1 28 (p.2 7) (p.2 8).toNat ++
      taFrame (p.2 2) (p.2 9) p.1 28) s₁.mem s₄.mem :=
    ((ta.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr)).trans
      (fr.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..)).trans
      ((co default).frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr))
  refine WP.mono (cr_exit hc h₁ (co default).env hf) fun s' ⟨abi, m'⟩ => ⟨abi, fun iv a c hr hl hct => ?_⟩
  have hA : ∀ i, i < 10 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  dsimp only
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide)] at hr
  rw [hA 3 (by decide), hA 4 (by decide)] at hl
  rw [hA 5 (by decide), hA 6 (by decide)] at hct
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), hA 7 (by decide), hA 8 (by decide), m']
  generalize hci : ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat = ciph at hr ⊢
  generalize hH : ctxH s₀.mem (w64 (p.2 0)) = H at hr ⊢
  have fE : Frame [⟨w64 (p.2 9) + BitVec.ofNat 64 96, 2464⟩] s₀.mem s₁.mem :=
    h₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hd := hin.data
  have hfit := hd.ok.fit
  have dP : ∀ r ∈ [pslotR (p.2 9)], (⟨w64 (p.2 7), (p.2 8).toNat⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.dw.sub_right (Lay.wSub (by decide))
  have hC1 : ciphOf s₁.mem (p.2 0) (p.2 1).toNat = ciph := by
    rw [← hci]; exact ciph_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) hc.rounds
  have hC3 : ciphOf s₃.mem (p.2 0) (p.2 1).toNat = ciph := by
    rw [← hC1, ciph_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) hc.rounds,
      ciph_frame ta.frame (ctx_taFrame L) hc.rounds]
  have hH1 : Hk s₁.mem (p.2 0) = H := by
    rw [← hH, ctxH_eq]; exact blockAt_frame fE fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hr₁ := streamRepr_frame fE (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.sb) hr
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr₁
  obtain ⟨hj, ha, hcr⟩ := hr₁
  have hD1 : bytesAt s₁.mem (w64 (p.2 7)) (p.2 8).toNat = bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat :=
    bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.dw.sub_right (Lay.wSub (by decide))) (by omega)
  have hab := ta.abs a c ⟨hl, hct⟩ (by rw [hH1]; exact ha)
  rw [hD1, hH1] at hab
  -- The counter blocks, as `crypt` takes them.
  have hct3 : CtrS s₃.mem (p.2 2) (ciphOf s₃.mem (p.2 0) (p.2 1).toNat) (inc32 (j0 H iv)) (p.2 6 ++ p.2 5).toNat := by
    rw [hC3, hct]
    have dP' : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [pslotR (p.2 9)],
        (⟨w64 (p.2 2) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
    exact (hcr.congr (blockAt_frame ta.frame (st_taFrame hc (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame ta.frame (st_taFrame hc (.inr ⟨by decide, by decide⟩)))).congr
      (blockAt_frame fr (dP' (by decide))) (blockAt_frame fr (dP' (by decide)))
  have hco := co (inc32 (j0 H iv))
  have hct₄ := hco.ctr hct3
  have hout := hco.out hct3
  rw [hC3] at hct₄ hout
  have hD3 : bytesAt s₃.mem (w64 (p.2 7)) (p.2 8).toNat = bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat := by
    rw [bytesAt_frame fr dP (by omega), bytesAt_frame ta.frame (data_taFrame hd.ok) (by omega), hD1]
  rw [hD3] at hout
  have hdrop : (gctr ciph (inc32 (j0 H iv)) (c ++ bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat)).drop c.length =
      xorKs ciph (inc32 (j0 H iv)) c.length (bytesAt s₀.mem (w64 (p.2 7)) (p.2 8).toNat) := by
    rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
  refine ⟨?_, by rw [hout, hdrop, hct]⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit]
  have dP' : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [pslotR (p.2 9)],
      (⟨w64 (p.2 2) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  refine ⟨?_, ?_, ?_⟩
  · have e₁ := blockAt_frame hco.frame (st_crFrame hc (d := 0) (k := 16) (by decide))
    have e₂ := blockAt_frame fr (dP' (d := 0) (k := 16) (by decide))
    have e₃ := blockAt_frame ta.frame (st_taFrame hc (d := 0) (k := 16) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂ e₃
    rw [e₁, e₂, e₃, hj]
  · exact (hab.congr (blockAt_frame fr (dP' (by decide)))
      (bytesAt_frame fr (dP' (d := 32) (k := (Spec.Gcm.ghashInput a _).length % 16) (by omega)) (by omega))).congr
      (blockAt_frame hco.frame (st_crFrame hc (by decide)))
      (bytesAt_frame hco.frame (st_crFrame hc (d := 32) (k := (Spec.Gcm.ghashInput a _).length % 16) (by omega))
        (by omega))
  · rw [List.length_append, length_bytesAt, ← hct]; exact hct₄

theorem streamDecrypt_correct (s : State) (hs : streamDecryptX86.pre s) :
    ∃ t s', Exec isa streamDecrypt s t s' ∧ abiPreserved s s' ∧ streamDecryptX86.post s s' :=
  (streamDecrypt_pc (pubOf 10 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamDecrypt_ct : ConstantTime isa streamDecryptX86.pre streamDecryptX86.pub streamDecrypt :=
  Pc.constantTime (pubOf 10) (fun _ _ _ _ h => pubOf_eq h) streamDecrypt_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86
