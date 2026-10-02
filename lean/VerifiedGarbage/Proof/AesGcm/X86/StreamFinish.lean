import VerifiedGarbage.Proof.AesGcm.X86.FinTag

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry, the tag
(`finTag 0`) and the exit, as one `Pc` (`streamFinish_pc`): correct
(`streamFinish_correct`) and constant time (`streamFinish_ct`). The entry
is shared with `vg_aes_gcm_stream_verify` (`finEntry_pc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph)

abbrev finKeeps : List (Nat × Nat) := [(0, ctxO), (1, roundsO), (3, alO), (4, ahO), (5, xlO), (6, xhO)]

theorem streamFinish_eq : (streamFinish vg.callees) = .seq (entry 7 (([.mov .esi (argOp 2)] : List Instr) ++
    ((finKeeps ++ []).flatMap (fun (p : Nat × Nat) => keep p.1 p.2) ++ []))) (.seq (finTag vg.callees 0) (.block restore)) := rfl

/-- What the precondition of `finish` and `verify` (with `nA` arguments) gives. -/
structure FinPre (nA : Nat) (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 256⟩]
  wr : s.wr = [⟨(arg s 2).setWidth 64, 80⟩, ⟨(arg s 7).setWidth 64, 2560⟩, ⟨argAddr s 0, 4 * nA⟩]
  cs : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 2), 80⟩
  cw : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 7), 2560⟩
  sw : (⟨w64 (arg s 2), 80⟩ : Region).Disjoint ⟨w64 (arg s 7), 2560⟩
  wa : (⟨w64 (arg s 7), 2560⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  r_s : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 2), 80⟩
  r_w : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 7), 2560⟩
  k_c : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 0), 256⟩
  k_s : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 2), 80⟩
  k_w : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 7), 2560⟩
  fc : (arg s 0).toNat + 256 ≤ 2 ^ 32
  fs : (arg s 2).toNat + 80 ≤ 2 ^ 32
  fw : (arg s 7).toNat + 2560 ≤ 2 ^ 32
  sp : 28 ≤ (s.gpr .esp).toNat
  fa : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32
  rounds : roundsOk s 1

theorem finPre_of {s : State} (h : finPre s) : FinPre 8 s := by
  simp only [finPre] at h
  obtain ⟨hrd, hwr, d_cs, d_cw, -, d_sw, -, d_wa, -, r_s, r_w, -, k_c, k_s, k_w, -, fc, fs, fw, sp, fa, hR⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_w
  exact ⟨hrd, hwr, d_cs, d_cw, d_sw, d_wa, r_s, r_w, k_c, k_s, k_w, fc, fs, fw, sp, by omega, hR⟩

theorem verifyPre_of {s : State} (h : verifyPre s) : FinPre 9 s := by
  simp only [verifyPre] at h
  obtain ⟨hrd, hwr, d_cs, d_cw, -, d_sw, -, d_wa, -, r_s, r_w, -, k_c, k_s, k_w, -, fc, fs, fw, sp, fa, hR⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_w
  exact ⟨hrd, hwr, d_cs, d_cw, d_sw, d_wa, r_s, r_w, k_c, k_s, k_w, fc, fs, fw, sp, by omega, hR⟩

theorem FinPre.lay {nA : Nat} {s : State} (h : FinPre nA s) : Lay (arg s 0) (arg s 2) (arg s 7) (s.gpr .esp) 28 :=
  ⟨h.fc, h.fs, h.fw, by decide, Nat.le_refl _, h.sp, h.cs, h.cw, h.sw.sub_right (Region.sub_prefix (by decide)),
    h.sw.sub_right (Lay.wSub (by decide)), h.k_c, h.k_s, h.k_w⟩

/-- After the entry of `finish` or `verify`. -/
structure FinEnt (nA : Nat) (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : FinPre nA s₀
  pub : pubOf nA s₀ = p
  fin : FinIn (p.2 0) (p.2 2) (p.2 7) p.1 (p.2 1).toNat (p.2 3) (p.2 4) (p.2 5) (p.2 6) s
  saved : SavedAt s.mem (p.2 7) s₀
  frame : Frame [⟨w64 (p.2 7) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The entry of `finish` and `verify`, copying also the arguments `ex`. -/
theorem finEntry_pc (nA : Nat) (hnA : 8 ≤ nA) (ex : List (Nat × Nat))
    (hex : ∀ q ∈ finKeeps ++ ex, q.1 < nA ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0)
    (hnd : ((finKeeps ++ ex).map (·.2)).Nodup) (Pre : State → Prop) (hPre : ∀ s, Pre s → FinPre nA s)
    (p : BitVec 32 × (Nat → BitVec 32))
    {hh : Taint.Hint VG.X86.taint.T}
    (ht : (VG.X86.taint.check (τr [.eax, .esp]) (.block (saveAt ++ (([.mov .esi (argOp 2)] : List Instr) ++
      ((finKeeps ++ ex).flatMap (fun p => keep p.1 p.2) ++ [])))) hh).isSome = true) :
    Pc (fun (s₀ : State) s => Pre s₀ ∧ pubOf nA s₀ = p ∧ s = s₀)
      (entry 7 (([.mov .esi (argOp 2)] : List Instr) ++ ((finKeeps ++ ex).flatMap (fun p => keep p.1 p.2) ++ [])))
      (fun s₀ s => FinEnt nA p s₀ s ∧ ∀ q ∈ ex, slotv s.mem (p.2 7) q.2 = arg s₀ q.1) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have h := hPre _ hpre
    have L := h.lay
    have a : ∀ i, i < nA → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have esp := pubOf_esp hpub
    have wW : Covers [⟨w64 (arg s₀ 7), 2560⟩] s₀.wr := by rw [h.wr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, h.rd, h.wr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) nA).Disjoint ⟨w64 (arg s₀ 7), 2560⟩ := by rw [argsR_eq]; exact h.wa.symm
    refine entry_ok (finKeeps ++ ex) [] (by omega) (by omega) hex hnd rfl rfl wW rA aw h.fa h.fw fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 2) (arg s₀ 7) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr, h.rd]; exact covers_of_mem (by simp),
        by rw [e.wr, h.wr]; exact covers_of_mem (by simp), by rw [e.wr]; exact wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨s₂, rfl, ⟨h, hpub, ?_, ?_, ?_, e.rd, e.wr⟩, fun q hq => by rw [← a 7 (by omega)]; exact e.slots q (by simp [hq])⟩
    · rw [← a 0 (by omega), ← a 1 (by omega), ← a 2 (by omega), ← a 3 (by omega), ← a 4 (by omega),
        ← a 5 (by omega), ← a 6 (by omega), ← a 7 (by omega), ← esp]
      exact ⟨he, e.slots (3, alO) (by simp), e.slots (4, ahO) (by simp), e.slots (5, xlO) (by simp),
        e.slots (6, xhO) (by simp), by rw [e.slots (1, roundsO) (by simp), ofNat_toNat32], h.rounds⟩
    · rw [← a 7 (by omega)]; exact e.saved
    · rw [← a 7 (by omega)]; exact e.frame
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 7 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) ht)
    subst s
    have h := hPre _ hpre
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, h.rd, h.wr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA h.fa (by omega))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by omega), by rw [sp]; exact pubOf_esp hpub⟩

/-- The exit of `finish` and `verify`, after the pieces wrote within `tagFrame St W SP 0`. -/
theorem fin_exit {nA : Nat} {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h₁ : FinEnt nA p s₀ s₁)
    (L : Lay (p.2 0) (p.2 2) (p.2 7) p.1 28) (he : Env (p.2 0) (p.2 2) (p.2 7) p.1 s)
    (hf : Frame (tagFrame (p.2 2) (p.2 7) p.1 0) s₁.mem s.mem) (hnA : 8 ≤ nA) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .eax = s.gpr .eax := by
  have esp := pubOf_esp h₁.pub
  have hp := h₁.pre
  have a : ∀ i, i < nA → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  have r_s := hp.r_s
  have r_w := hp.r_w
  have sp := hp.sp
  rw [esp, a 2 (by omega)] at r_s
  rw [esp, a 7 (by omega)] at r_w
  rw [esp] at sp
  have hsv : SavedAt s.mem (p.2 7) s₀ := h₁.saved.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm
  have rT : ∀ r ∈ tagFrame (p.2 2) (p.2 7) p.1 0, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact r_s.sub_right (Region.sub_prefix (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact ret_below sp
  have rE : ∀ r ∈ [(⟨w64 (p.2 7) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, ret_kept hf rT, ret_kept h₁.frame rE]
  exact WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) L.fw hsv hret)
    fun s' ⟨abi, m', ax, _, _⟩ => ⟨abi, m', ax⟩

/-- The streaming state and the key context, as the pieces see them after the entry. -/
theorem fin_repr {nA : Nat} {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ : State} (h₁ : FinEnt nA p s₀ s₁)
    (L : Lay (p.2 0) (p.2 2) (p.2 7) p.1 28) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {iv a c : List Byte}
    (hr : StreamRepr s₀.mem (w64 (p.2 2)) (ctxCiph s₀.mem (w64 (p.2 0)) R) (ctxH s₀.mem (w64 (p.2 0))) iv a c) :
    StreamRepr s₁.mem (w64 (p.2 2)) (ciphOf s₁.mem (p.2 0) R) (Hk s₁.mem (p.2 0)) iv a c ∧
      ciphOf s₁.mem (p.2 0) R = ctxCiph s₀.mem (w64 (p.2 0)) R ∧ Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
  have hC : ciphOf s₁.mem (p.2 0) R = ctxCiph s₀.mem (w64 (p.2 0)) R :=
    ciph_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) hR
  have hH : Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
    rw [ctxH_eq]
    exact blockAt_frame h₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  refine ⟨?_, hC, hH⟩
  rw [hC, hH]
  exact streamRepr_frame h₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 2432) (by decide) (.inr ⟨by decide, by decide⟩)) hr

theorem streamFinish_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => finPre s₀ ∧ pubOf 8 s₀ = p ∧ s = s₀) (streamFinish vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamFinishX86.post s₀ s') := by
  by_cases hex : ∃ s₀, finPre s₀ ∧ pubOf 8 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay (p.2 0) (p.2 2) (p.2 7) p.1 28 := by
    have := (finPre_of hz).lay
    rwa [pubOf_arg hzp (i := 0) (by decide), pubOf_arg hzp (i := 2) (by decide),
      pubOf_arg hzp (i := 7) (by decide), pubOf_esp hzp] at this
  have hR : (p.2 1).toNat = 10 ∨ (p.2 1).toNat = 12 ∨ (p.2 1).toNat = 14 := by
    have := (finPre_of hz).rounds; rwa [roundsOk, pubOf_arg hzp (i := 1) (by decide)] at this
  rw [streamFinish_eq]
  refine Pc.seq (finEntry_pc 8 (by decide) [] (by decide) (by decide) finPre (fun _ h => finPre_of h) p
    (by taint_decide)) (Pc.seq (Pc.lift (finTag_pc L (o := 0) (.inl rfl)) (fun _ s => s.mem)
      fun s₀ s h => ⟨h.1.fin, rfl⟩) ?_)
  refine Pc.taint [.ebp] (fun s₀ s ⟨s₁, ⟨h₁, _⟩, ho, _, _⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  refine WP.mono (fin_exit h₁ L ho.env ho.frame (by decide)) fun s' ⟨abi, m', _⟩ => ⟨abi, fun iv a c hr hl ht => ?_⟩
  have hA : ∀ i, i < 8 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide)] at hr
  rw [hA 3 (by decide), hA 4 (by decide)] at hl
  rw [hA 5 (by decide), hA 6 (by decide)] at ht
  rw [hA 0 (by decide), hA 1 (by decide), hA 7 (by decide), m']
  obtain ⟨hr₁, hC, hH⟩ := fin_repr h₁ L hR hr
  have := ho.tag iv a c hr₁ hl ht
  have e0 : w64 (p.2 7) + BitVec.ofNat 64 0 = w64 (p.2 7) := BitVec.add_zero _
  rw [hC, hH, e0] at this
  exact this

theorem streamFinish_correct (s : State) (hs : streamFinishX86.pre s) :
    ∃ t s', Exec isa (streamFinish vg.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishX86.post s s' :=
  (streamFinish_pc (pubOf 8 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamFinish_ct : ConstantTime isa streamFinishX86.pre streamFinishX86.pub (streamFinish vg.callees) :=
  Pc.constantTime (pubOf 8) (fun _ _ _ _ h => pubOf_eq h) streamFinish_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86
