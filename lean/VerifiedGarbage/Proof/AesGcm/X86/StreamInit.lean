import VerifiedGarbage.Proof.AesGcm.X86.J0

/-!
# AES-GCM on x86: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. The entry, `J₀` and the
first counter block (`j0`) and the exit, as one `Pc` (`streamInit_pc`):
correct (`streamInit_correct`) and constant time (`streamInit_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)
open VG.Proof.Gcm (Absorbed Ctr)

abbrev siTail : List Instr := [.mov .eax (imm 0), .store (at_ .ebp zO) .eax]
abbrev siKeeps : List (Nat × Nat) := [(0, ctxO), (1, dO), (2, nO), (2, nlO)]

theorem streamInit_eq : streamInit = .seq (entry 4 ([.mov .esi (argOp 3)] ++
    (siKeeps.flatMap (fun p => keep p.1 p.2) ++ siTail))) (.seq j0 (.block restore)) := rfl

theorem streamInit_lay {s : State} (h : streamInitPre s) :
    Lay (arg s 0) (arg s 3) (arg s 4) (s.gpr .esp) 24 := by
  simp only [streamInitPre] at h
  obtain ⟨-, -, d_cs, d_cw, -, -, -, -, d_sw, -, -, -, -, -, -, -, k_c, -, k_s, k_w, -, fc, -, fs, fw, sp, -⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_w
  exact ⟨fc, fs, fw, Nat.le_refl _, by decide, sp, d_cs, d_cw, d_sw.sub_right (Region.sub_prefix (by decide)),
    d_sw.sub_right (Lay.wSub (by decide)), k_c, k_s, k_w⟩

/-- After the entry: the nonce ready for `j0`. -/
structure SiIn (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : streamInitPre s₀
  pub : pubOf 5 s₀ = p
  j : J0In (p.2 0) (p.2 3) (p.2 4) p.1 24 (p.2 1) (p.2 2).toNat s
  saved : SavedAt s.mem (p.2 4) s₀
  frame : Frame [⟨w64 (p.2 4) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem siEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamInitPre s₀ ∧ pubOf 5 s₀ = p ∧ s = s₀)
      (entry 4 ([.mov .esi (argOp 3)] ++ (siKeeps.flatMap (fun p => keep p.1 p.2) ++ siTail)))
      (SiIn p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have L := streamInit_lay hpre
    have hp := hpre
    simp only [streamInitPre] at hp
    obtain ⟨hrd, hwr, -, -, -, d_ns, d_nw, -, -, -, d_wa, -, -, -, -, -, -, k_n, -, -, -,
      -, fn, -, fw, sp, fa⟩ := hp
    have a : ∀ i, i < 5 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have esp := pubOf_esp hpub
    rw [ofNat_lit, below_eq sp] at k_n
    have wW : Covers [⟨w64 (arg s₀ 4), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 5] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 5).Disjoint ⟨w64 (arg s₀ 4), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    refine entry_ok siKeeps siTail (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw
      (by omega) fw fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 3) (arg s₀ 4) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr, hrd]; exact covers_of_mem (by simp),
        by rw [e.wr, hwr]; exact covers_of_mem (by simp), by rw [e.wr]; exact wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨_, by xrun [he.ebp, L.aW, he.wIn], ?_⟩
    have hf : Frame [⟨w64 (arg s₀ 4) + BitVec.ofNat 64 zO, 4⟩] s₂.mem
        (s₂.mem.writeW (w64 (arg s₀ 4) + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have sl : ∀ {o}, 128 ≤ o → o + 4 ≤ 2560 → (o + 4 ≤ zO ∨ zO + 4 ≤ o) → slotv (s₂.mem.writeW
        (w64 (arg s₀ 4) + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)) (arg s₀ 4) o = slotv s₂.mem (arg s₀ 4) o :=
      fun h₁ h₂ h₃ => slot_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h₃ (by omega) (by decide)
    refine ⟨hpre, hpub, ?_, ?_, ?_, by mems [e.rd], by mems [e.wr]⟩
    rotate_left
    · rw [← a 4 (by decide)]
      simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact e.saved.frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [← a 4 (by decide)]
      simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact e.frame.trans (hf.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)
    rw [← a 0 (by decide), ← a 1 (by decide), ← a 2 (by decide), ← a 3 (by decide), ← a 4 (by decide), ← esp]
    refine ⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) ?_, ?_, ?_, ?_, ?_,
      ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact sl (by decide) (by decide) (by decide)
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide) (by decide)]
      exact e.slots (1, dO) (by simp)
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide) (by decide)]
      rw [e.slots (2, nO) (by simp), ofNat_toNat32]
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sl (by decide) (by decide) (by decide)]
      rw [e.slots (2, nlO) (by simp), ofNat_toNat32]
    · simp only [mem_setMem, mem_setReg, mem_arithFlags, slotv_eq, Mem.readW_writeW_self32]; rfl
    · exact (arg s₀ 2).isLt
    · mems [e.rd, e.wr, hrd]; exact covers_of_mem (by simp)
    · exact fn
    · exact d_ns
    · exact d_nw
    · exact k_n
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 4 ∧ s.gpr .esp = p.1)
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
    simp only [streamInitPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 5] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

theorem si_ret {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (h : streamInitPre s₀) (hp : pubOf 5 s₀ = p) :
    (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 3), 80⟩ ∧ (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 4), 2560⟩ ∧
      24 ≤ p.1.toNat := by
  simp only [streamInitPre] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, r_s, r_w, -, -, -, -, -, -, -, -, -, -, sp, -⟩ := h
  rw [pubOf_arg hp (i := 3) (by decide), pubOf_arg hp (i := 4) (by decide), pubOf_esp hp] at *
  exact ⟨r_s, r_w, sp⟩

theorem streamInit_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamInitPre s₀ ∧ pubOf 5 s₀ = p ∧ s = s₀) streamInit
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamInitX86.post s₀ s') := by
  by_cases hex : ∃ s₀, streamInitPre s₀ ∧ pubOf 5 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay (p.2 0) (p.2 3) (p.2 4) p.1 24 := by
    have := streamInit_lay hz
    rwa [pubOf_arg hzp (i := 0) (by decide), pubOf_arg hzp (i := 3) (by decide),
      pubOf_arg hzp (i := 4) (by decide), pubOf_esp hzp] at this
  obtain ⟨r_s, r_w, sp⟩ := si_ret hz hzp
  rw [streamInit_eq]
  refine Pc.seq (siEntry_pc p) (Pc.seq (Pc.lift (j0_pc L) (fun _ s => s.mem) fun s₀ s h => ⟨h.j, rfl⟩) ?_)
  refine Pc.taint [.ebp] (fun s₀ s ⟨s₁, h₁, ho, rd, wr⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have he := ho.env
  have esp := pubOf_esp h₁.pub
  have a : ∀ i, i < 5 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  have fE := h₁.frame
  have fJ := ho.frame
  have hsv : SavedAt s.mem (p.2 4) s₀ := h₁.saved.frameK fJ (kept_j0Frame L)
  have rJ : ∀ r ∈ j0Frame (p.2 3) (p.2 4) p.1 24, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact r_s
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact r_w.sub_right (Lay.wSub (by decide))
    · exact ret_below sp
  have rE : ∀ r ∈ [(⟨w64 (p.2 4) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, ret_kept fJ rJ, ret_kept fE rE]
  refine WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) L.fw hsv hret)
    fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, fun ciph => ?_⟩
  have hp := h₁.pre
  simp only [streamInitPre] at hp
  obtain ⟨-, -, -, -, -, -, d_nw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fn, -, -, -, -⟩ := hp
  rw [a 1 (by decide), a 2 (by decide), a 4 (by decide)] at d_nw
  rw [a 1 (by decide), a 2 (by decide)] at fn
  rw [a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide)]
  have hH : Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
    rw [ctxH_eq]
    exact blockAt_frame fE fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hD : bytesAt s₁.mem (w64 (p.2 1)) (p.2 2).toNat = bytesAt s₀.mem (w64 (p.2 1)) (p.2 2).toNat :=
    bytesAt_frame (p := w64 (p.2 1)) (n := (p.2 2).toNat) fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact d_nw.sub_right (Lay.wSub (d := 128) (n := 2432) (by decide))) (by omega)
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, m', Proof.Gcm.ghashInput_nil]
  refine ⟨by rw [ho.j0, hH, hD], Proof.Gcm.absorbed_nil _ ho.y, Proof.Gcm.ctr_zero _ _ _ _ ?_⟩
  rw [ho.cb, hH, hD]

theorem streamInit_correct (s : State) (hs : streamInitX86.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ streamInitX86.post s s' :=
  (streamInit_pc (pubOf 5 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamInit_ct : ConstantTime isa streamInitX86.pre streamInitX86.pub streamInit :=
  Pc.constantTime (pubOf 5) (fun _ _ _ _ h => pubOf_eq h) streamInit_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86
