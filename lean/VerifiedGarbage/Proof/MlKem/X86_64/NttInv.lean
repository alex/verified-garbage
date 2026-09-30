import VerifiedGarbage.Proof.MlKem.X86_64.Ntt

/-!
# ML-KEM on x86-64: `vg_mlkem_inv_ntt`

Untrusted: everything here is checked by Lean. As `vg_mlkem_ntt`
(`Ntt.lean`): each layer is `nttInvLayer`, the seven layers are those of
`NTT⁻¹` (`nttInv_eq_layers`), and the last pass multiplies each coefficient
by 3303 (`vscale_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem nttInvLayer_eq (F : Poly) (len : Nat) :
    nttInvLayer F len = layF nttInvBlockN F len (fun c => 256 / len - 1 - c) (128 / len) := rfl

/-- A layer of `NTT⁻¹` with `len ≥ 8`, whose first zeta is `zeta k`. -/
theorem invLay_ok {sP : Addr} (len k : Nat) (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 256 / len - 1 = k)
    {F : Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay vibfly len k (-2)) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F len) ∧ BInv sP s s' := by
  have hl : 128 / len ≥ 1 ∧ 256 / len = 2 * (128 / len) ∧ 256 / len ≤ 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [nttInvLayer_eq]
  exact vlay_ok vibfly_spec nttInvBlk_ok hlen (-2) (fun c => 256 / len - 1 - c) (by rw [hk]; rfl)
    (fun c _ => by omega)
    (fun c hc' => step_bwd (zi := fun c => 256 / len - 1 - c) (dz := -2) _ 1 (by decide) (by omega))
    hc hsi hS hT hw

theorem invLay4_ok {sP : Addr} {F : Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay4 vibfly 62 0x05 (-4)) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 4) ∧ BInv sP s s' := by
  rw [nttInvLayer_eq, show 256 / 4 - 1 = 63 from rfl, show 128 / 4 = 32 from rfl]
  exact vlay4_ok vibfly_spec nttInvBlk_ok 62 0x05 (-4) (fun c => 63 - c) (fun i => 62 - 2 * i) rfl (by decide)
    (by decide)
    (fun i hi => step_bwd (zi := fun i => 62 - 2 * i) (dz := -4) _ 2 (by decide) (by omega))
    hc hsi hS hT hw

theorem invLay2_ok {sP : Addr} {F : Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 vibfly 124 0x1B (-8)) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 2) ∧ BInv sP s s' := by
  rw [nttInvLayer_eq, show 256 / 2 - 1 = 127 from rfl, show 128 / 2 = 64 from rfl]
  exact vlay2_ok vibfly_spec nttInvBlk_ok 124 0x1B (-8) (fun c => 127 - c) (fun i => 124 - 4 * i) rfl
    (by decide) (by decide)
    (fun i hi => step_bwd (zi := fun i => 124 - 4 * i) (dz := -8) _ 4 (by decide) (by omega))
    hc hsi hS hT hw

theorem nttInv_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.nttInv s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa Impl.MlKem.X86_64.nttInv s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold Impl.MlKem.X86_64.nttInv
    refine withMxcsr_ok rfl hw ?_ fun s1 k1 f1 => ?_
    · decide +kernel
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.seq (WP.mono (vpro_ok hdi1 hsi1 hF1 (by rw [k1.2.2]; exact hwf) (by rw [k1.2.2]; exact hw) hd)
      fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine LI.seq hsi2 hw2 invLay2_ok ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LI.seq hsi2 hw2 invLay4_ok ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 8 31 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 16 15 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 32 7 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 64 3 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (invLay_ok 128 1 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fun _ hc hsi hS _ hw => vscale_ok hc hsi hS hw) ?_ hI
    intro s3 hI
    refine WP.mono (vepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4, _⟩ => ⟨?_, ?_⟩
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

theorem nttInv_ct : ConstantTime isa (inPlaceK nttInv).pre (inPlaceK nttInv).pub Impl.MlKem.X86_64.nttInv :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

theorem nttInv_verified :
    Verified X86_64.target Impl.MlKem.X86_64.nttInv (Spec.MlKem.nttInvContract X86_64.abi) :=
  Verified.of_correct nttInv_correct nttInv_ct (by
    mlkem_implies [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlKem.X86_64
