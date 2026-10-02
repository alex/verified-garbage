import VerifiedGarbage.Proof.AesGcm.X86.TextAbsorb

/-!
# AES-GCM on x86: the entry of `stream_encrypt` and `stream_decrypt`

Untrusted: everything here is checked by Lean. What the precondition
gives (`CrPure`), the entry (`crEntry_pc`), the text as `crypt` takes it
(`setText_ok`) and as `textAbsorb` takes it.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph)

abbrev crKeeps : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (3, alO), (4, ahO), (5, xlO), (6, xhO), (7, dataO), (8, lenO)]

/-- The facts of the precondition about the public data `p` alone. -/
structure CrPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  lay : Lay (p.2 0) (p.2 2) (p.2 9) p.1 28
  fd : (p.2 7).toNat + (p.2 8).toNat ≤ 2 ^ 32
  dctx : (⟨w64 (p.2 0), 256⟩ : Region).Disjoint ⟨w64 (p.2 7), (p.2 8).toNat⟩
  dst : (⟨w64 (p.2 7), (p.2 8).toNat⟩ : Region).Disjoint ⟨w64 (p.2 2), 80⟩
  dw : (⟨w64 (p.2 7), (p.2 8).toNat⟩ : Region).Disjoint ⟨w64 (p.2 9), 2560⟩
  dstk : (below p.1 28).Disjoint ⟨w64 (p.2 7), (p.2 8).toNat⟩
  r_s : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 80⟩
  r_d : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 7), (p.2 8).toNat⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 9), 2560⟩
  sp : 28 ≤ p.1.toNat
  rounds : (p.2 1).toNat = 10 ∨ (p.2 1).toNat = 12 ∨ (p.2 1).toNat = 14

theorem crPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : streamCryptPre s) (hp : pubOf 10 s = p) :
    CrPure p := by
  simp only [streamCryptPre] at h
  obtain ⟨-, -, d_cs, d_cd, d_cw, -, d_sd, d_sw, -, d_dw, -, -, -, r_s, r_d, r_w, -, k_c, k_s, k_d, k_w, -,
    fc, fs, fd, fw, sp, -, hR⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_d k_w
  have a0 := pubOf_arg hp (i := 0) (by decide); have a1 := pubOf_arg hp (i := 1) (by decide)
  have a2 := pubOf_arg hp (i := 2) (by decide); have a7 := pubOf_arg hp (i := 7) (by decide)
  have a8 := pubOf_arg hp (i := 8) (by decide); have a9 := pubOf_arg hp (i := 9) (by decide)
  have e := pubOf_esp hp
  simp only [roundsOk] at hR
  simp only [a0, a1, a2, a7, a8, a9, e] at d_cs d_cd d_cw d_sd d_sw d_dw r_s r_d r_w k_c k_s k_d k_w fc fs fd fw sp hR
  exact ⟨⟨fc, fs, fw, by decide, Nat.le_refl _, sp, d_cs, d_cw, d_sw.sub_right (Region.sub_prefix (by decide)),
    d_sw.sub_right (Lay.wSub (by decide)), k_c, k_s, k_w⟩, fd, d_cd, d_sd.symm, d_dw, k_d, r_s, r_d, r_w, sp, hR⟩

/-- After the entry of `stream_encrypt` or `stream_decrypt`. -/
structure CEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : streamCryptPre s₀
  pub : pubOf 10 s₀ = p
  env : Env (p.2 0) (p.2 2) (p.2 9) p.1 s
  rounds : RoundsAt s.mem (p.2 9) (p.2 1).toNat
  ta : TaSl (p.2 9) (p.2 7) (p.2 8).toNat (p.2 3) (p.2 5) (p.2 6) s.mem
  ah : slotv s.mem (p.2 9) ahO = p.2 4
  saved : SavedAt s.mem (p.2 9) s₀
  frame : Frame [⟨w64 (p.2 9) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem crEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamCryptPre s₀ ∧ pubOf 10 s₀ = p ∧ s = s₀)
      (entry 9 (([.mov .esi (argOp 2)] : List Instr) ++ (crKeeps.flatMap (fun p => keep p.1 p.2) ++ []))) (CEnt p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hp := hpre
    simp only [streamCryptPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, d_wa, -, -, -, -, -, -, -, -, -, -, -, -, -, fw, -, fa, hR⟩ := hp
    have a : ∀ i, i < 10 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have esp := pubOf_esp hpub
    have wW : Covers [⟨w64 (arg s₀ 9), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 10] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 10).Disjoint ⟨w64 (arg s₀ 9), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    refine entry_ok crKeeps [] (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw (by omega) fw
      fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 2) (arg s₀ 9) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr, hrd]; exact covers_of_mem (by simp),
        by rw [e.wr, hwr]; exact covers_of_mem (by simp), by rw [e.wr]; exact wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨s₂, rfl, hpre, hpub, ?_, ?_, ?_, ?_, ?_, ?_, e.rd, e.wr⟩
    · rw [← a 0 (by decide), ← a 2 (by decide), ← a 9 (by decide), ← esp]; exact he
    · rw [← a 1 (by decide), ← a 9 (by decide)]
      exact ⟨by rw [e.slots (1, roundsO) (by simp), ofNat_toNat32], hR⟩
    · rw [← a 3 (by decide), ← a 5 (by decide), ← a 6 (by decide), ← a 7 (by decide), ← a 8 (by decide),
        ← a 9 (by decide)]
      exact ⟨e.slots (7, dataO) (by simp), by rw [e.slots (8, lenO) (by simp), ofNat_toNat32],
        e.slots (3, alO) (by simp), e.slots (5, xlO) (by simp), e.slots (6, xhO) (by simp)⟩
    · rw [← a 4 (by decide), ← a 9 (by decide)]; exact e.slots (4, ahO) (by simp)
    · rw [← a 9 (by decide)]; exact e.saved
    · rw [← a 9 (by decide)]; exact e.frame
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 9 ∧ s.gpr .esp = p.1)
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
    simp only [streamCryptPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 10] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

/-- `setText`: the text as the pieces take it. -/
theorem setText_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K) {D : BitVec 32} {n : Nat}
    {al xl xh : BitVec 32} {s : State} (he : Env Ctx St W SP s) (hs : TaSl W D n al xl xh s.mem) :
    ∃ s', runBlock isa setText s = some s' ∧ slotv s'.mem W dO = D ∧ slotv s'.mem W nO = BitVec.ofNat 32 n ∧
      slotv s'.mem W bO = BitVec.ofNat 32 (xl.toNat % 16) ∧ Frame [pslotR W] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h1 := hs.data; have h2 := hs.len; have h3 := hs.xl
  rw [slotv_eq] at h1 h2 h3
  simp only [dataO, lenO, xlO] at h1 h2 h3
  have hand := and15 xl
  refine ⟨_, by xrun [setText, he.ebp, L.aW, he.wIn, he.wIn', h1, h2, h3], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]
  · mems [slotv_eq, h2]
  · mems [slotv_eq, h3]; rw [hand]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
      (by decide) _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  all_goals rfl

end VG.Proof.AesGcm.X86
