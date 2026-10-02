import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize

/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_finalize` is correct

Untrusted: everything here is checked by Lean. After the branch on the
length, `eax:edx` holds `Mₙ` (`BPost`); the function XORs in the chaining
value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as the state, the MAC
(`macFull_split8`).
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.X86 (Upd Mupd wp_movm wp_store wp_bswap)

theorem finalize_wp {s₀ : State} (h0 : finalizeX86.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeX86.post s₀ s' := by
  have hp := FPre.of h0
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have tf := hp.st_fit
  have tf' : (arg s₀ 1).toNat + 8 ≤ 2 ^ 32 := hp.st_fit
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  have rdwr₁ : s₁.rd ++ s₁.wr = [keyR s₀, lastR s₀, argsR s₀, fstR s₀, fscrR s₀] := by
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have stIn : ∀ d, d + 4 ≤ 8 → InRegions (s₁.rd ++ s₁.wr) ((FSt s₀).setWidth 64 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr₁]; exact in_rw (r := fstR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have mnS : ∀ r ∈ [mnR s₀], Region.Sub r (fstR s₀) ∨ Region.Sub r (fscrR s₀) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Or.inr (Offset.sub_base _ (by decide))
  -- `finMid`.
  refine WP.seq ?_
  simp only [finMid, stk]
  refine wp_arg (s₀ := s₀) 1 rfl h₁.esp (hp.argIn h₁.rd h₁.wr (by decide)) (hp.arg_eq h₁.frame mnS (by decide))
    fun s₂ u₂ => ?_
  refine wp_xorma (a := (FSt s₀).setWidth 64) (by rw [u₂.gpr, addr_zero])
    (by rw [u₂.rd, u₂.wr]; simpa [add0] using stIn 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_xorma (a := (FSt s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [u₃.other .ecx (by decide), u₂.gpr]; exact addr_eq (by omega))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_bswap fun s₅ u₅ => wp_bswap fun s₆ u₆ => WP.block_nil ?_
  have g₆ : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s₆.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2, u₅.other _ hr.1, u₄.other _ hr.2.2, u₃.other _ hr.1, u₂.other _ hr.2.1]
  have mem₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have ax₆ : s₆.gpr .eax ++ s₆.gpr .edx =
      byteRev64 ((s₁.gpr .edx ++ s₁.gpr .eax) ^^^ s₁.mem.readW ((FSt s₀).setWidth 64) 64) := by
    rw [u₆.gpr, u₆.other .eax (by decide), u₅.gpr, u₅.other .edx (by decide), u₄.gpr, u₄.other .eax (by decide),
      u₃.gpr, u₃.other .edx (by decide), u₂.other .eax (by decide), u₂.other .edx (by decide), u₃.mem,
      u₂.mem, bswap_xor_append,
      readW64_split s₁.mem]
  have esi₆ : s₆.gpr .esi = FW s₀ := by rw [g₆ _ (by decide), h₁.esi]
  have ebp₆ : s₆.gpr .ebp = FS s₀ := by rw [g₆ _ (by decide), h₁.ebp]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr]
  have bp : BlockPre s₆ :=
    { sched := ⟨400, by rw [esi₆, rd₆, wr₆, hp.rd]; simp, by decide, by rw [esi₆]; exact kf⟩
      scr := ⟨640, by rw [ebp₆, wr₆, hp.wr]; simp, by decide, by rw [ebp₆]; exact sf⟩
      disj := by
        rw [esi₆, ebp₆]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₇ ⟨same₇, esi₇, ax₇⟩ => ?_)
  let A := (FS s₀).setWidth 64
  have xR₆ : xR s₆ = ⟨A, 84⟩ := by rw [xR, ebp₆]
  have f₇ : Frame [⟨A, 84⟩] s₁.mem s₇.mem := by rw [← mem₆, ← xR₆]; exact same₇.frame
  have F₇ : Frame [mnR s₀, ⟨A, 84⟩] (savedMem s₀ (FS s₀)) s₇.mem :=
    (h₁.frame.mono (by simp)).trans (f₇.mono (by simp))
  have F₇S : ∀ r ∈ [mnR s₀, ⟨A, 84⟩], Region.Sub r (fstR s₀) ∨ Region.Sub r (fscrR s₀) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (Offset.sub_base _ (by decide))
    · exact Or.inr (Region.sub_prefix (by decide))
  have esp₇ : s₇.gpr .esp = s₀.gpr .esp := by rw [same₇.esp, g₆ _ (by decide), h₁.esp]
  have ebp₇ : s₇.gpr .ebp = FS s₀ := by rw [same₇.ebp, ebp₆]
  have rd₇ : s₇.rd = s₀.rd := by rw [same₇.rd, rd₆]
  have wr₇ : s₇.wr = s₀.wr := by rw [same₇.wr, wr₆]
  rw [WP.block_append_iff]
  refine wp_arg (s₀ := s₀) 1 rfl esp₇ (hp.argIn rd₇ wr₇ (by decide)) (hp.arg_eq F₇ F₇S (by decide))
    fun s₈ u₈ => wp_bswap fun s₉ u₉ => wp_bswap fun s₁₀ u₁₀ => ?_
  have stW : ∀ d, d + 4 ≤ 8 → InRegions s₁₀.wr ((FSt s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇, hp.wr]
    exact in_rw (r := fstR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_store (a := (FSt s₀).setWidth 64) (by rw [ea_at', u₁₀.other _ (by decide), u₉.other _ (by decide),
    u₈.gpr, addr_zero]) (by simpa [add0] using stW 0 (by decide)) fun s₁₁ w₁₁ => ?_
  refine wp_store (a := (FSt s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [ea_at', w₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]; exact addr_eq (by omega))
    (by rw [w₁₁.wr]; exact stW 4 (by decide)) fun s₁₂ w₁₂ => WP.block_nil ?_
  have ebp₁₂ : s₁₂.gpr .ebp = FS s₀ := by
    rw [w₁₂.gpr, w₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), ebp₇]
  have mem₁₂ : s₁₂.mem = (s₇.mem.writeW ((FSt s₀).setWidth 64) (bswap (s₇.gpr .eax))).writeW
      ((FSt s₀).setWidth 64 + BitVec.ofNat 64 4) (bswap (s₇.gpr .edx)) := by
    rw [w₁₂.mem, w₁₁.mem, w₁₁.gpr, u₁₀.gpr, u₁₀.other .eax (by decide), u₉.gpr, u₁₀.mem, u₉.mem,
      u₉.other .edx (by decide), u₈.other .eax (by decide), u₈.other .edx (by decide), u₈.mem]
  have rdwr₁₂ : s₁₂.rd ++ s₁₂.wr = [keyR s₀, lastR s₀, argsR s₀, fstR s₀, fscrR s₀] := by
    rw [w₁₂.rd, w₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, w₁₂.wr, w₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, rd₇, wr₇, hp.rd, hp.wr]; rfl
  have c0 : (fstR s₀).Contains ((FSt s₀).setWidth 64) (32 / 8) := by
    simpa [add0] using Offset.contains_base ((FSt s₀).setWidth 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  have c4 : (fstR s₀).Contains ((FSt s₀).setWidth 64 + BitVec.ofNat 64 4) (32 / 8) :=
    Offset.contains_base _ (by decide) (by omega)
  have F₁₂ : Frame [mnR s₀, ⟨A, 84⟩, fstR s₀] (savedMem s₀ (FS s₀)) s₁₂.mem := by
    rw [mem₁₂]
    exact ((F₇.mono (by simp)).writeW (r := fstR s₀) (by simp) _ c0).writeW (r := fstR s₀) (by simp) _ c4
  -- The slots of the saved registers.
  have slots : ∀ d, 84 ≤ d → d + 4 ≤ 100 →
      s₁₂.mem.readW (A + BitVec.ofNat 64 d) 32 = (savedMem s₀ (FS s₀)).readW (A + BitVec.ofNat 64 d) 32 := by
    intro d h₁' h₂'
    refine F₁₂.readW (r := ⟨A + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm
  have ret : s₁₂.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
    rw [F₁₂.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact (savedMem_frame s₀ (FS s₀)).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))
      · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))
      · exact hp.ret_st
  refine WP.mono (restore_ok ebp₁₂ (by omega) fun d h₁' h₂' => by
      rw [rdwr₁₂]; exact in_rw (r := fscrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    fun s' ⟨hl, ho, m', _, _⟩ => ⟨restored slots hl (by
      rw [ho _ (by decide), w₁₂.gpr, w₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), esp₇]) (by rw [m', ret]), ?_⟩
  intro hk msg hml hne hst
  have F₈ : Frame [fscrR s₀] s₀.mem s₇.mem := by
    refine ((savedMem_frame s₀ (FS s₀)).sub fun r hr => ⟨fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
      (F₇.sub fun r hr => ⟨fscrR s₀, by simp, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub_base _ (by decide)
    · exact Region.sub_prefix (by decide)
  have F₁ : Frame [fscrR s₀] s₀.mem s₁.mem :=
    ((savedMem_frame s₀ (FS s₀)).sub fun r hr => ⟨fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
    (h₁.frame.sub fun r hr => ⟨fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩)
  have hS' : sch s₆ = Spec.TripleDes.scheduleAt s₀.mem ((FW s₀).setWidth 64) := by
    show Spec.TripleDes.scheduleAt s₆.mem ((s₆.gpr .esi).setWidth 64) = _
    rw [esi₆, mem₆]
    exact scheduleAt_frame F₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.key_scr.sub_left (Region.sub_prefix (by decide))
  have hst₁ : le8 (s₁.mem.readW ((FSt s₀).setWidth 64) 64) = Spec.Aes.bytesAt s₀.mem ((FSt s₀).setWidth 64) 8 := by
    rw [le8_readW]
    exact bytesAt_frame F₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr) (by decide)
  have hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem ((FW s₀).setWidth 64))
  have hk' : Spec.Aes.bytesAt s₀.mem ((FW s₀).setWidth 64 + BitVec.ofNat 64 384) 8 ++
      Spec.Aes.bytesAt s₀.mem ((FW s₀).setWidth 64 + BitVec.ofNat 64 392) 8 =
      (Spec.Cmac.subkeys (ciphAt s₀.mem ((FW s₀).setWidth 64)) 8).1 ++
        (Spec.Cmac.subkeys (ciphAt s₀.mem ((FW s₀).setWidth 64)) 8).2 := by
    rw [show (FW s₀).setWidth 64 + BitVec.ofNat 64 392 =
        (FW s₀).setWidth 64 + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
      (Offset.add_add _ 384 8).symm, ← bytesAt_split]; exact hk
  obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, ciphAt, hks, length_le8])
  show Spec.Aes.bytesAt s'.mem ((FSt s₀).setWidth 64) 8 = _
  rw [m', mem₁₂, ← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi, bswap_eq, bswap_eq,
    byteRev32_append, ax₇, ax₆, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
    macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, Proof.Cmac.xor_comm]

end VG.Proof.CmacTripleDes.X86
