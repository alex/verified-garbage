import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
import VerifiedGarbage.Proof.MlKem.X86_64.NttInv

/-!
# ML-KEM on x86-64: `vg_mlkem_ntt_avx2` and `vg_mlkem_inv_ntt_avx2`

Untrusted: everything here is checked by Lean. As `vg_mlkem_ntt` and
`vg_mlkem_inv_ntt` (`Ntt.lean`, `NttInv.lean`), on sixteen words at a time:
the prologue leaves the table of zetas (in the order the layers read it) and
`f` as words in `scratch` (`ypro_ok`), each layer is `nttLayer` or
`nttInvLayer` (`ylay_ok`, `ylay8_ok`, `ylay4_ok`, `ylay2_ok`), and the
epilogue unpacks `S` into `f` (`yepi_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The butterflies in each lane -/

theorem lane_vbfly : laneSseBlock (toY vbfly) = some vbfly := by decide +kernel
theorem lane_vibfly : laneSseBlock (toY vibfly) = some vibfly := by decide +kernel
theorem lane_vbfly4 : laneSseBlock (toY (gath4 ++ vbfly ++ scat4)) = some (gath4 ++ vbfly ++ scat4) := by
  decide +kernel
theorem lane_vibfly4 : laneSseBlock (toY (gath4 ++ vibfly ++ scat4)) = some (gath4 ++ vibfly ++ scat4) := by
  decide +kernel
theorem lane_vbfly2 : laneSseBlock (toY (gath2 ++ vbfly ++ scat2)) = some (gath2 ++ vbfly ++ scat2) := by
  decide +kernel
theorem lane_vibfly2 : laneSseBlock (toY (gath2 ++ vibfly ++ scat2)) = some (gath2 ++ vibfly ++ scat2) := by
  decide +kernel

/-! ## The layers of `NTT` -/

/-- A layer of `NTT` with `len ≥ 16`, whose first zeta is `zeta t`. -/
theorem fwdLayY_ok {sP : Addr} (len t : Nat) (hlen : len ∈ [16, 32, 64, 128]) (ht : 128 / len = t)
    {F : Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : TZ s.mem sP zeta) (hw : pR sP ∈ s.wr) :
    WP isa (ylay vbfly len t) s fun s' => S16 s'.mem (spW sP) (nttLayer F len) ∧ BInvY sP s s' := by
  subst ht
  have h8 : 128 / len ≤ 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl <;> decide
  rw [nttLayer_eq]
  exact ylay_ok vbfly_spec lane_vbfly nttBlk_ok hlen (fun c => 128 / len + c) (fun c _ => ⟨by omega, rfl⟩)
    hc hsi hS hT hw

theorem fwdLay8Y_ok {sP : Addr} {F : Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : TZ s.mem sP zeta) (hw : pR sP ∈ s.wr) :
    WP isa (ylay8 vbfly 16) s fun s' => S16 s'.mem (spW sP) (nttLayer F 8) ∧ BInvY sP s s' := by
  rw [nttLayer_eq]
  exact ylay8_ok vbfly_spec lane_vbfly nttBlk_ok (fun c => 16 + c) (fun c hc' => ⟨by omega, rfl⟩) hc hsi hS hT hw

theorem fwdLay4Y_ok {sP : Addr} {F : Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : TZ s.mem sP zeta) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 vbfly 32) s fun s' => S16 s'.mem (spW sP) (nttLayer F 4) ∧ BInvY sP s s' := by
  rw [nttLayer_eq]
  exact ylay4_ok vbfly_spec nttBlk_ok lane_vbfly4 (fun c => 32 + c) (fun c hc' => ⟨by omega, rfl⟩) hc hsi hS hT hw

theorem fwdLay2Y_ok {sP : Addr} {F : Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : TZ s.mem sP zeta) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 vbfly 64) s fun s' => S16 s'.mem (spW sP) (nttLayer F 2) ∧ BInvY sP s s' := by
  rw [nttLayer_eq]
  exact ylay2_ok vbfly_spec nttBlk_ok lane_vbfly2 (fun c => 64 + c) (fun c hc' => ⟨by omega, rfl⟩) hc hsi hS hT hw

/-! ## The layers of `NTT⁻¹` -/

/-- The zetas of `NTT⁻¹` in the order its layers read them. -/
abbrev zInv (k : Nat) : Zq := zeta (127 - k)

theorem zmTabInv_eq (k : Nat) : zmTabInv k = (zInv k).val * 65536 % 3329 := zmTab_eq _

/-- A layer of `NTT⁻¹` with `len ≥ 16`, whose zetas start at entry `t` of
the table. -/
theorem invLayY_ok {sP : Addr} (len t : Nat) (hlen : len ∈ [16, 32, 64, 128])
    (ht : ∀ c < 128 / len, t + c < 128 ∧ 127 - (t + c) = 256 / len - 1 - c)
    {F : Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : TZ s.mem sP zInv) (hw : pR sP ∈ s.wr) :
    WP isa (ylay vibfly len t) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F len) ∧ BInvY sP s s' := by
  rw [nttInvLayer_eq]
  exact ylay_ok vibfly_spec lane_vibfly nttInvBlk_ok hlen (fun c => 256 / len - 1 - c) (z := zInv)
    (fun c hc' => ⟨(ht c hc').1, congrArg zeta (ht c hc').2⟩) hc hsi hS hT hw

theorem invLay8Y_ok {sP : Addr} {F : Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : TZ s.mem sP zInv) (hw : pR sP ∈ s.wr) :
    WP isa (ylay8 vibfly 96) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 8) ∧ BInvY sP s s' := by
  rw [nttInvLayer_eq]
  exact ylay8_ok vibfly_spec lane_vibfly nttInvBlk_ok (fun c => 31 - c) (z := zInv)
    (fun c hc' => ⟨by omega, congrArg zeta (by omega)⟩) hc hsi hS hT hw

theorem invLay4Y_ok {sP : Addr} {F : Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : TZ s.mem sP zInv) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 vibfly 64) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 4) ∧ BInvY sP s s' := by
  rw [nttInvLayer_eq]
  exact ylay4_ok vibfly_spec nttInvBlk_ok lane_vibfly4 (fun c => 63 - c) (z := zInv)
    (fun c hc' => ⟨by omega, congrArg zeta (by omega)⟩) hc hsi hS hT hw

theorem invLay2Y_ok {sP : Addr} {F : Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : TZ s.mem sP zInv) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 vibfly 0) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 2) ∧ BInvY sP s s' := by
  rw [nttInvLayer_eq]
  exact ylay2_ok vibfly_spec nttInvBlk_ok lane_vibfly2 (fun c => 127 - c) (z := zInv)
    (fun c hc' => ⟨by omega, congrArg zeta (by omega)⟩) hc hsi hS hT hw

/-! ## `vg_mlkem_ntt_avx2` -/

theorem nttY_correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa nttAvx2 s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttAvx2 s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold nttAvx2
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw ?_ fun s1 k1 f1 => ?_
    · decide +kernel
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.seq (WP.mono (ypro_ok zmTab zmTab_eq hdi1 hsi1 hF1 (by rw [k1.2.2]; exact hwf)
      (by rw [k1.2.2]; exact hw) hd) fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine LIY.seq hsi2 hw2 (fwdLayY_ok 128 1 (by decide) (by decide)) ?_
      ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LIY.seq hsi2 hw2 (fwdLayY_ok 64 2 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (fwdLayY_ok 32 4 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (fwdLayY_ok 16 8 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 fwdLay8Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 fwdLay4Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 fwdLay2Y_ok ?_ hI
    intro s3 hI
    refine WP.mono (yepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4⟩ => ⟨?_, ?_⟩
    · rw [ntt_eq_layers]
      simp only [nttLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_))) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr (mx_sub _), .inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _)) hP

theorem nttY_ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub nttAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

theorem nttY_verified : Verified X86_64.target nttAvx2 (Spec.MlKem.nttContract X86_64.abi) :=
  Verified.of_correct nttY_correct nttY_ct (by
    mlkem_implies [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

/-! ## `vg_mlkem_inv_ntt_avx2` -/

theorem nttInvY_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa nttInvAvx2 s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttInvAvx2 s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold nttInvAvx2
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw ?_ fun s1 k1 f1 => ?_
    · decide +kernel
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.seq (WP.mono (ypro_ok zmTabInv zmTabInv_eq hdi1 hsi1 hF1 (by rw [k1.2.2]; exact hwf)
      (by rw [k1.2.2]; exact hw) hd) fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine LIY.seq hsi2 hw2 invLay2Y_ok ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LIY.seq hsi2 hw2 invLay4Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 invLay8Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (invLayY_ok 16 112 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (invLayY_ok 32 120 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (invLayY_ok 64 124 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (invLayY_ok 128 126 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (fun _ hc hsi hS _ hw => yscale_ok hc hsi hS hw) ?_ hI
    intro s3 hI
    refine WP.mono (yepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4⟩ => ⟨?_, ?_⟩
    · rw [nttInv_eq_layers]
      simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_))) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr (mx_sub _), .inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _)) hP

theorem nttInvY_ct : ConstantTime isa (inPlaceK nttInv).pre (inPlaceK nttInv).pub nttInvAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

theorem nttInvY_verified : Verified X86_64.target nttInvAvx2 (Spec.MlKem.nttInvContract X86_64.abi) :=
  Verified.of_correct nttInvY_correct nttInvY_ct (by
    mlkem_implies [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlKem.X86_64
