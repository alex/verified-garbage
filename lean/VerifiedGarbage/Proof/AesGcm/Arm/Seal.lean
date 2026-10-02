import VerifiedGarbage.Proof.AesGcm.Arm.OneShot

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. `seal` keeps a streaming
state at `W + 16`: `J₀` and the additional data (`oneAad`), the data
encrypted in place (`oneCrypt`), and the tag of the ciphertext into `W`
(`oneTag 0`) (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr encryptWith toBytes)
open VG.Proof.Gcm (Absorbed)

section
variable {n : Nat}

theorem one_dataW {s₀ s : State} (h : onePre n s₀) (hk : ArgsKeep n s₀ s) (k7 k8 : BitVec 32) :
    DataW (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 k8 s (arg s₀ 2) (arg s₀ 3).toNat :=
  ⟨one_dataOk h hk, by rw [hk.wr, h.2.1]; exact covers_of_mem (by simp), h.2.2.1⟩

theorem saved_otFrame {s₀ : State} (h : onePre n s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ otFrame (oSt s₀) (arg s₀ 4) s₀.sp o, (savedR (arg s₀ 4)).Disjoint r := by
  have L := oneLay h
  have hst := oSt_addr h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hst]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by omega)) (by decide) (by omega)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- What `seal`'s pieces leave, from the entry on. -/
theorem seal_mid {s₀ s₁ s₂ s₃ : State} (h : onePre n s₀) (h1 : SO1 n s₀ s₁) (oa : OA n s₀ s₁.mem s₂)
    {k7 : BitVec 32} (oc : OC n s₀ k7 (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))) s₂.mem s₃) :
    blockAt s₃.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) ∧
    Absorbed s₃.mem (State.addr (oSt s₀) + BitVec.ofNat 64 16) (State.addr (oSt s₀) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat ++
        zeros (padLen (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat).length)) ∧
    blockAt s₃.mem (State.addr (oSt s₀)) =
      j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat) ∧
    ciphOf s₃.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
      ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat ∧
    bytesAt s₃.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
          (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)))
        (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat) ∧
    SavedAt s₃.mem (arg s₀ 4) s₀ := by
  have L := oneLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hd := one_dataW h oa.args 0 0
  have dCr := ctx_crFrame L hd
  have dc₂ : ∀ r ∈ [savedR (arg s₀ 4)] ++ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp,
      (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | hr
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
  have f₂ : Frame ([savedR (arg s₀ 4)] ++ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp) s₀.mem s₂.mem :=
    (h1.frame.mono fun r hr => List.mem_append_left _ hr).trans (oa.frame.mono fun r hr => List.mem_append_right _ hr)
  have hc₂ := ciph_keep f₂ dc₂ hR
  have hD₂ : bytesAt s₂.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat := by
    have hp := h
    obtain ⟨-, -, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -⟩ := hp
    exact bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with rfl | hr
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact one_dataJ0 h dDW bD r hr) (by have := hd.ok.lt; omega)
  have hb := Nat.mod_lt (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat ++
    zeros (padLen (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat).length)).length (show 16 > 0 by decide)
  refine ⟨?_, (oa.abs.congr (blockAt_frame oc.frame (stp_crFrame L hd (by decide)))
      (bytesAt_frame oc.frame (stp_crFrame L hd (by omega)) (by omega))), ?_,
    by rw [ciph_frame oc.frame dCr hR, hc₂], by rw [oc.out, hc₂, hD₂],
    (h1.saved.frame oa.frame (saved_j0Frame L)).frame oc.frame (saved_crFrame L hd)⟩
  · rw [blockAt_frame oc.frame (fun r hr => (dCr r hr).sub_left (Lay.ctxSub (by decide)))]; exact oa.hH
  · rw [blockAt_frame oc.frame (by simpa using stp_crFrame L hd (d := 0) (k := 16) (by decide))]; exact oa.j

end

theorem seal_wp {s₀ : State} (h : sealArm.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' := by
  have h' : onePre 5 s₀ := h
  have L := oneLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine WP.seq (one1_wp h' (by decide) fun s₁ h1 => WP.seq (WP.mono (oneAad_ok h' (by decide) h1) fun s₂ oa => ?_))
  obtain ⟨k7, he₂⟩ := oa.env
  refine WP.seq (WP.mono (oneCrypt_ok h' (by decide) he₂ oa.args oa.cb) fun s₃ oc => ?_)
  have he₃ := oc.env
  obtain ⟨hH₃, hab₃, hj₃, hc₃, hD₃, sv₃⟩ := seal_mid h' h1 oa oc
  refine WP.seq (WP.mono (oneTag_ok h' (by decide) (o := 0) (.inl rfl) he₃ oc.args hH₃ (length_bytesAt _ _ _).symm hab₃)
    fun s₄ ot => ?_)
  obtain ⟨k7'', he₄⟩ := ot.env
  refine WP.mono (restore_ok he₄.r11 fW (covers_left he₄.perm.w) (sv₃.frame ot.frame (saved_otFrame h' (.inl rfl)))
    he₄.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm := hh.2.1
  have hpre := h'
  obtain ⟨-, -, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -⟩ := hpre
  have hD₄ : bytesAt s₄.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      bytesAt s₃.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat := by
    refine bytesAt_frame ot.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [oSt_addr h']; exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact bD.symm
  have ho := ot.out
  rw [hc₃, hj₃, add_ofNat_zero, ← Proof.Gcm.fullTag_eq] at ho
  simp only [sealArm, encryptWith, hm, hD₄, hD₃, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by
    rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Cmac.toBytes_length])

end VG.Proof.AesGcm.Arm
