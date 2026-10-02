import VerifiedGarbage.Proof.AesGcm.X86.Top

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The entry, the additional
data absorbed into GHASH (`absorb 16`) and the exit, as one `Pc`
(`streamAad_pc`): correct (`streamAad_correct`) and constant time
(`streamAad_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

abbrev aadTail : List Instr := [.mov .eax (argOp 2), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax]
abbrev aadKeeps : List (Nat × Nat) := [(0, ctxO), (4, dO), (5, nO)]

theorem streamAad_eq : streamAad = .seq (entry 6 ([.mov .esi (argOp 1)] ++
    (aadKeeps.flatMap (fun p => keep p.1 p.2) ++ aadTail))) (.seq (absorb 16) (.block restore)) := rfl

theorem streamAad_lay {s : State} (h : streamAadPre s) :
    Lay (arg s 0) (arg s 1) (arg s 6) (s.gpr .esp) 24 := by
  simp only [streamAadPre] at h
  obtain ⟨-, -, d_cs, d_cw, -, -, d_sw, -, -, -, -, -, -, -, -, -, k_c, k_s, -, k_w, -, fc, fs, -, fw, sp, -⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_w
  exact ⟨fc, fs, fw, Nat.le_refl _, by decide, sp, d_cs, d_cw, d_sw.sub_right (Region.sub_prefix (by decide)),
    d_sw.sub_right (Lay.wSub (by decide)), k_c, k_s, k_w⟩

/-- After the entry: the additional data ready for `absorb 16`. -/
structure AadIn (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : streamAadPre s₀
  pub : pubOf 7 s₀ = p
  abs : AbsIn (p.2 0) (p.2 1) (p.2 6) p.1 24 (p.2 4) (p.2 5).toNat ((p.2 2).toNat % 16) s
  saved : SavedAt s.mem (p.2 6) s₀
  frame : Frame [⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem aadEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamAadPre s₀ ∧ pubOf 7 s₀ = p ∧ s = s₀)
      (entry 6 ([.mov .esi (argOp 1)] ++ (aadKeeps.flatMap (fun p => keep p.1 p.2) ++ aadTail)))
      (AadIn p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have L := streamAad_lay hpre
    have hp := hpre
    simp only [streamAadPre] at hp
    obtain ⟨hrd, hwr, d_cs, d_cw, d_ca, d_sd, d_sw, d_sa, d_dw, d_da, d_wa, -, -, -, -, -, k_c, k_s, k_d, k_w, k_a,
      fc, fs, fd, fw, sp, fa⟩ := hp
    have a : ∀ i, i < 7 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have esp := pubOf_esp hpub
    rw [ofNat_lit, below_eq sp] at k_d
    have wW : Covers [⟨w64 (arg s₀ 6), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 7] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 7).Disjoint ⟨w64 (arg s₀ 6), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    refine entry_ok aadKeeps aadTail (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw
      (by omega) fw fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 1) (arg s₀ 6) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr, hrd]; exact covers_of_mem (by simp),
        by rw [e.wr, hwr]; exact covers_of_mem (by simp), by rw [e.wr]; exact wW,
        e.slots (0, ctxO) (by simp)⟩
    have i₂ : InRegions (s₂.rd ++ s₂.wr) (argA (s₀.gpr .esp) 2) 4 := by
      rw [e.rd, e.wr]; exact argIn_of rA (by omega) (by decide)
    have v₂ := e.args 2 (by decide)
    have hand := and15 (arg s₀ 2)
    refine ⟨_, by xrun [e.esp, i₂, v₂, he.ebp, L.aW, he.wIn], ?_⟩
    have hf : Frame [⟨w64 (arg s₀ 6) + BitVec.ofNat 64 bO, 4⟩] s₂.mem
        (s₂.mem.writeW (w64 (arg s₀ 6) + BitVec.ofNat 64 bO) (arg s₀ 2 &&& BitVec.ofNat 32 15)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have sl : ∀ {o}, 128 ≤ o → o + 4 ≤ 280 → slotv (s₂.mem.writeW (w64 (arg s₀ 6) + BitVec.ofNat 64 bO)
        (arg s₀ 2 &&& BitVec.ofNat 32 15)) (arg s₀ 6) o = slotv s₂.mem (arg s₀ 6) o := fun h₁ h₂ =>
      slot_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    refine ⟨hpre, hpub, ?_, ?_, ?_, by mems [e.rd], by mems [e.wr]⟩
    rotate_left
    · rw [← a 6 (by decide)]
      simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact e.saved.frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [← a 6 (by decide)]
      simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact e.frame.trans (hf.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)
    rw [← a 0 (by decide), ← a 1 (by decide), ← a 2 (by decide), ← a 4 (by decide), ← a 5 (by decide),
      ← a 6 (by decide), ← esp]
    refine ⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) ?_, ?_, ?_, ?_,
      Nat.mod_lt _ (by decide), (arg s₀ 5).isLt, ⟨?_, fd, d_sd.symm, d_dw, k_d⟩⟩
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact sl (by decide) (by decide)
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide)]
      exact e.slots (4, dO) (by simp)
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide)]
      rw [e.slots (5, nO) (by simp), ofNat_toNat32]
    · simp only [mem_setMem, mem_setReg, mem_arithFlags, slotv_eq, Mem.readW_writeW_self32]
      rw [hand]
    · mems [e.rd, e.wr, hrd]; exact covers_of_mem (by simp)
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 6 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [streamAadPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 7] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

/-- The facts of the precondition the exit needs, in terms of the public data. -/
theorem aad_ret {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (h : streamAadPre s₀) (hp : pubOf 7 s₀ = p) :
    (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 1), 80⟩ ∧ (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 6), 2560⟩ ∧
      24 ≤ p.1.toNat := by
  simp only [streamAadPre] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, r_s, -, r_w, -, -, -, -, -, -, -, -, -, -, sp, -⟩ := h
  rw [pubOf_arg hp (i := 1) (by decide), pubOf_arg hp (i := 6) (by decide), pubOf_esp hp] at *
  exact ⟨r_s, r_w, sp⟩

theorem streamAad_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamAadPre s₀ ∧ pubOf 7 s₀ = p ∧ s = s₀) streamAad
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamAadX86.post s₀ s') := by
  by_cases hex : ∃ s₀, streamAadPre s₀ ∧ pubOf 7 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay (p.2 0) (p.2 1) (p.2 6) p.1 24 := by
    have := streamAad_lay hz
    rwa [pubOf_arg hzp (i := 0) (by decide), pubOf_arg hzp (i := 1) (by decide),
      pubOf_arg hzp (i := 6) (by decide), pubOf_esp hzp] at this
  obtain ⟨r_s, r_w, sp⟩ := aad_ret hz hzp
  rw [streamAad_eq]
  refine Pc.seq (aadEntry_pc p) (Pc.seq (Pc.lift (absorb_pc L (yo := 16) (.inr rfl) (Nat.mod_lt _ (by decide))
    (p.2 5).isLt) (fun _ s => s.mem) fun s₀ s h => ⟨h.abs, rfl⟩) ?_)
  refine Pc.taint [.ebp] (fun s₀ s ⟨s₁, h₁, ho, rd, wr⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have he := ho.env
  have esp := pubOf_esp h₁.pub
  have a : ∀ i, i < 7 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  -- What the entry and `absorb` write.
  have fE := h₁.frame
  have fA := ho.frame
  have dE : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [(⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩ : Region)],
      (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  have dA : ∀ {d k : Nat}, (d + k ≤ 16 ∨ (48 ≤ d ∧ d + k ≤ 80)) → ∀ r ∈ absFrame (p.2 1) (p.2 6) p.1 24 16,
      (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega)).symm
  have hsv : SavedAt s.mem (p.2 6) s₀ := h₁.saved.frame fA fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  have rA : ∀ r ∈ absFrame (p.2 1) (p.2 6) p.1 24 16, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact r_s.sub_right (Lay.stSub (by decide))
    · exact r_s.sub_right (Lay.stSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact ret_below sp
  have rE : ∀ r ∈ [(⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, ret_kept fA rA, ret_kept fE rE]
  refine WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) L.fw hsv hret)
    fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, fun ciph iv x hr hl => ?_⟩
  have hp := h₁.pre
  simp only [streamAadPre] at hp
  obtain ⟨-, -, -, -, -, -, -, -, d_dw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fd, -, -, -⟩ := hp
  rw [a 4 (by decide), a 5 (by decide), a 6 (by decide)] at d_dw
  rw [a 4 (by decide), a 5 (by decide)] at fd
  rw [a 0 (by decide), a 1 (by decide)] at hr
  rw [a 0 (by decide), a 1 (by decide), a 4 (by decide), a 5 (by decide)]
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  have hH : Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
    rw [ctxH_eq]
    exact blockAt_frame fE fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hD : bytesAt s₁.mem (w64 (p.2 4)) (p.2 5).toNat = bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat :=
    bytesAt_frame (p := w64 (p.2 4)) (n := (p.2 5).toNat) fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_dw.sub_right (Lay.wSub (d := 128) (n := 2432) (by decide))) (by omega)
  have hx : x.length % 16 = (p.2 2).toNat % 16 := by rw [← a 2 (by decide), lo_mod16 hl]
  rw [Proof.Gcm.ghashInput_nil] at ha ⊢
  rw [m']
  refine ⟨?_, ?_, ?_⟩
  · rw [← hj]
    have e₁ := blockAt_frame fA (dA (d := 0) (k := 16) (.inl (by decide)))
    have e₂ := blockAt_frame fE (dE (d := 0) (k := 16) (by decide))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂
    rw [e₁, e₂]
  · have ha₁ : Absorbed s₁.mem (w64 (p.2 1) + BitVec.ofNat 64 16) (w64 (p.2 1) + BitVec.ofNat 64 32)
        (Hk s₁.mem (p.2 0)) x := by
      rw [hH]
      exact ha.congr (blockAt_frame fE (dE (by decide))) (bytesAt_frame fE (dE (d := 32) (k := x.length % 16) (by omega)) (by omega))
    have := ho.abs x hx ha₁
    rwa [hH, hD] at this
  · exact hc.congr (by rw [blockAt_frame fA (dA (.inr ⟨by decide, by decide⟩)),
      blockAt_frame fE (dE (by decide))]) (by rw [blockAt_frame fA (dA (.inr ⟨by decide, by decide⟩)),
      blockAt_frame fE (dE (by decide))])

theorem streamAad_correct (s : State) (hs : streamAadX86.pre s) :
    ∃ t s', Exec isa streamAad s t s' ∧ abiPreserved s s' ∧ streamAadX86.post s s' :=
  (streamAad_pc (pubOf 7 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamAad_ct : ConstantTime isa streamAadX86.pre streamAadX86.pub streamAad :=
  Pc.constantTime (pubOf 7) (fun _ _ _ _ h => pubOf_eq h) streamAad_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86
