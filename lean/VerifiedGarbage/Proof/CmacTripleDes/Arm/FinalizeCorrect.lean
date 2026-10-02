import VerifiedGarbage.Proof.CmacTripleDes.Arm.Finalize

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_finalize` is correct

Untrusted: everything here is checked by Lean. After the branch on the
length, `r4:r5` holds `Mₙ` (`BPost`); the function saves the state pointer,
XORs in the chaining value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as
the state, the MAC (`macFull_split8`).
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_ldr wp_str wp_rev)

theorem finalize_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeArm.post s₀ s' := by
  have hp := FPre.of h0
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have tf := hp.st_fit
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  have rdwr₁ : s₁.rd ++ s₁.wr = [keyR s₀, lastR s₀, fargsR s₀, fstR s₀, fscrR s₀] := by
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have stIn : ∀ d, d + 4 ≤ 8 → InRegions (s₁.rd ++ s₁.wr) (State.addr (FSt s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr₁]; exact in_rw (r := fstR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  -- `finMid`.
  refine WP.seq ?_
  simp only [finMid]
  refine wp_str (by decide) (by rw [h₁.r10, hp.scrAddr (by decide)]) (by rw [h₁.wr]; exact hp.inScr (by decide) (by decide))
    fun s₂ w₂ => ?_
  refine wp_ldr (by decide) (by rw [w₂.gpr, h₁.r1, add0]) (by rw [w₂.rd, w₂.wr]; simpa using stIn 0 (by decide))
    fun s₃ u₃ => ?_
  refine wp_ldr (a := State.addr (FSt s₀) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.other _ (by decide), w₂.gpr, h₁.r1]; exact addr_add (by omega))
    (by rw [u₃.rd, u₃.wr, w₂.rd, w₂.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_eor (op2_reg _ _) fun s₅ u₅ => wp_eor (op2_reg _ _) fun s₆ u₆ => wp_rev fun s₇ u₇ =>
    wp_rev fun s₈ u₈ => WP.block_nil ?_
  have g₈ : ∀ r, r ∉ [Reg.r0, .r1, .r4, .r5, .r6, .r7] → s₈.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₈.other _ hr.2.1, u₇.other _ hr.1, u₆.other _ hr.2.2.2.1, u₅.other _ hr.2.2.1, u₄.other _ hr.2.2.2.2.2,
      u₃.other _ hr.2.2.2.2.1, w₂.gpr]
  let A := State.addr (FS s₀)
  have mem₈ : s₈.mem = s₁.mem.writeW (A + BitVec.ofNat 64 112) (FSt s₀) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, w₂.mem, h₁.r1]
  have stSep : ∀ d, d + 4 ≤ 8 →
      (s₁.mem.writeW (A + BitVec.ofNat 64 112) (FSt s₀)).readW (State.addr (FSt s₀) + BitVec.ofNat 64 d) 32 =
        s₁.mem.readW (State.addr (FSt s₀) + BitVec.ofNat 64 d) 32 := fun d hd =>
    Mem.readW_writeW_sep ((hp.st_scr.sub_right (Offset.sub_base _ (by decide))).sub_left
      (Offset.sub_base _ (by omega)) |>.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
  have ax₈ : s₈.gpr .r0 ++ s₈.gpr .r1 =
      byteRev64 ((s₁.gpr .r5 ++ s₁.gpr .r4) ^^^ s₁.mem.readW (State.addr (FSt s₀)) 64) := by
    have e0 := stSep 0 (by decide)
    have e4 := stSep 4 (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e0
    rw [u₈.gpr, u₈.other .r0 (by decide), u₇.gpr, u₇.other .r5 (by decide), u₆.gpr, u₆.other .r4 (by decide),
      u₅.gpr, u₅.other .r5 (by decide), u₅.other .r7 (by decide), u₄.gpr, u₄.other .r4 (by decide),
      u₄.other .r5 (by decide), u₄.other .r6 (by decide), u₃.gpr, u₃.other .r4 (by decide), u₃.other .r5 (by decide),
      u₃.mem, w₂.mem, w₂.gpr, h₁.r1, e0, e4, rev_xor_append, readW64_split s₁.mem]
  have r9₈ : s₈.gpr .r9 = FW s₀ := by rw [g₈ _ (by decide), h₁.r9]
  have r10₈ : s₈.gpr .r10 = FS s₀ := by rw [g₈ _ (by decide), h₁.r10]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, w₂.rd, h₁.rd]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂.wr, h₁.wr]
  have bp : BlockPre s₈ :=
    { sched := ⟨400, (by rw [r9₈, rd₈, wr₈, hp.rd]; simp), (by decide), (by rw [r9₈]; exact kf)⟩
      scr := ⟨640, (by rw [r10₈, wr₈, hp.wr]; simp), (by decide), (by rw [r10₈]; exact sf)⟩
      disj := by
        rw [r9₈, r10₈]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₉ ⟨same₉, r9₉, ax₉⟩ => ?_)
  have r10₉ : s₉.gpr .r10 = FS s₀ := by rw [same₉.r10, g₈ _ (by decide), h₁.r10]
  have xR₈ : xR s₈ = ⟨A, 52⟩ := by rw [xR, g₈ _ (by decide), h₁.r10]
  have f₉ : Frame [⟨A, 52⟩] s₈.mem s₉.mem := by rw [← xR₈]; exact same₉.frame
  have outBlock : ∀ d, 52 ≤ d → d + 4 ≤ 640 →
      s₉.mem.readW (A + BitVec.ofNat 64 d) 32 = s₈.mem.readW (A + BitVec.ofNat 64 d) 32 := fun d h₁' h₂' =>
    f₉.readW (r := ⟨A + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have rdwr₉ : s₉.rd ++ s₉.wr = [keyR s₀, lastR s₀, fargsR s₀, fstR s₀, fscrR s₀] := by
    rw [same₉.rd, same₉.wr, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, w₂.rd, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr,
      u₃.wr, w₂.wr, rdwr₁]
  have wr₉ : s₉.wr = [fstR s₀, fscrR s₀] := by
    rw [same₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂.wr, h₁.wr, hp.wr]
  rw [WP.block_append_iff]
  refine wp_ldr (by decide) (by rw [r10₉, hp.scrAddr (by decide)])
    (by rw [rdwr₉]; exact in_rw (r := fscrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun s₁₀ u₁₀ => ?_
  have r2₁₀ : s₁₀.gpr .r2 = FSt s₀ := by
    rw [u₁₀.gpr, outBlock 112 (by decide) (by decide), mem₈, Mem.readW_writeW_self32]
  refine wp_rev fun s₁₁ u₁₁ => wp_rev fun s₁₂ u₁₂ => ?_
  have stW : ∀ d, d + 4 ≤ 8 → InRegions s₁₂.wr (State.addr (FSt s₀) + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉]
    exact in_rw (r := fstR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_str (by decide) (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), r2₁₀, add0])
    (by simpa using stW 0 (by decide)) fun s₁₃ w₁₃ => ?_
  refine wp_str (a := State.addr (FSt s₀) + BitVec.ofNat 64 4) (by decide)
    (by rw [w₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), r2₁₀]; exact addr_add (by omega))
    (by rw [w₁₃.wr]; exact stW 4 (by decide)) fun s₁₄ w₁₄ => WP.block_nil ?_
  have r10₁₄ : s₁₄.gpr .r10 = FS s₀ := by
    rw [w₁₄.gpr, w₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), r10₉]
  have mem₁₄ : s₁₄.mem = (s₉.mem.writeW (State.addr (FSt s₀)) (rev (s₉.gpr .r0))).writeW
      (State.addr (FSt s₀) + BitVec.ofNat 64 4) (rev (s₉.gpr .r1)) := by
    rw [w₁₄.mem, w₁₃.mem, w₁₃.gpr, u₁₂.gpr, u₁₂.other .r0 (by decide), u₁₁.gpr, u₁₂.mem, u₁₁.mem,
      u₁₁.other .r1 (by decide), u₁₀.other .r0 (by decide), u₁₀.other .r1 (by decide), u₁₀.mem]
  have rdwr₁₄ : s₁₄.rd ++ s₁₄.wr = [keyR s₀, lastR s₀, fargsR s₀, fstR s₀, fscrR s₀] := by
    rw [w₁₄.rd, w₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, w₁₄.wr, w₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, rdwr₉]
  -- The slots of the saved registers.
  have slots : ∀ d, 52 ≤ d → d + 4 ≤ 88 →
      s₁₄.mem.readW (A + BitVec.ofNat 64 d) 32 = (savedMem s₀ (FS s₀)).readW (A + BitVec.ofNat 64 d) 32 := by
    intro d h₁' h₂'
    have sd : ∀ e, e + 4 ≤ 8 → Mem.Sep (A + BitVec.ofNat 64 d) (32 / 8) (State.addr (FSt s₀) + BitVec.ofNat 64 e) (32 / 8) :=
      fun e he => (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm.sub_right (Offset.sub_base _ (by omega))
        |>.sep (Region.contains_self _ _) (Region.contains_self _ _)
    have sd0 := sd 0 (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at sd0
    rw [mem₁₄, Mem.readW_writeW_sep (sd 4 (by decide)) (by decide), Mem.readW_writeW_sep sd0 (by decide),
      outBlock d (by omega) (by omega), mem₈, readW_writeW_far _ _ _ (by omega) (by decide) (by omega)]
    refine h₁.frame.readW (r := ⟨A + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine WP.mono (restore_ok r10₁₄ (by omega) fun d h₁' h₂' => by
      rw [rdwr₁₄]; exact in_rw (r := fscrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    fun s' ⟨hl, sp', m', _, _⟩ => ⟨restored slots hl (by
      rw [sp', w₁₄.sp, w₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, same₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, w₂.sp,
        h₁.sp]), ?_⟩
  intro hk msg hml hne hst
  have scrSub : ∀ r ∈ [mnR s₀], ∃ r' ∈ [fscrR s₀], Region.Sub r r' := fun r hr => ⟨fscrR s₀, by simp, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩
  have F₁ : Frame [fscrR s₀] s₀.mem s₁.mem :=
    ((savedMem_frame s₀ (FS s₀)).sub fun r hr => ⟨fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
    (h₁.frame.sub scrSub)
  have F₈ : Frame [fscrR s₀] s₀.mem s₈.mem := by
    rw [mem₈]; exact F₁.writeW (r := fscrR s₀) (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega))
  have hS' : sch s₈ = Spec.TripleDes.scheduleAt s₀.mem (State.addr (FW s₀)) := by
    show Spec.TripleDes.scheduleAt s₈.mem (State.addr (s₈.gpr .r9)) = _
    rw [r9₈]
    exact scheduleAt_frame F₈ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.key_scr.sub_left (Region.sub_prefix (by decide))
  have hst₁ : le8 (s₁.mem.readW (State.addr (FSt s₀)) 64) = Spec.Aes.bytesAt s₀.mem (State.addr (FSt s₀)) 8 := by
    rw [le8_readW]
    exact bytesAt_frame F₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr) (by decide)
  have hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem (State.addr (FW s₀)))
  have hk' : Spec.Aes.bytesAt s₀.mem (State.addr (FW s₀) + BitVec.ofNat 64 384) 8 ++
      Spec.Aes.bytesAt s₀.mem (State.addr (FW s₀) + BitVec.ofNat 64 392) 8 =
      (Spec.Cmac.subkeys (ciphAt s₀.mem (State.addr (FW s₀))) 8).1 ++
        (Spec.Cmac.subkeys (ciphAt s₀.mem (State.addr (FW s₀))) 8).2 := by
    rw [show State.addr (FW s₀) + BitVec.ofNat 64 392 =
        State.addr (FW s₀) + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
      (Offset.add_add _ 384 8).symm, ← bytesAt_split]; exact hk
  obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, ciphAt, hks, length_le8])
  show Spec.Aes.bytesAt s'.mem (State.addr (FSt s₀)) 8 = _
  rw [m', mem₁₄, ← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi, rev_eq, rev_eq,
    byteRev32_append, ax₉, ax₈, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
    macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, Proof.Cmac.xor_comm]

end VG.Proof.CmacTripleDes.Arm
