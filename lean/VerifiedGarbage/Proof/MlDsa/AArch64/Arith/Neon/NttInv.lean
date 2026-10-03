import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Scale

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (inPlaceK)
open VG.Spec.MlDsa (PolyIs polyAt)

theorem nttInv_noCalls : VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv.noCalls = true := by lit_decide

theorem nttInv_correct (s : State) (hs : (inPlaceK Spec.MlDsa.nttInv).pre s) :
    ∃ t s', Exec isa VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv s t s' ∧ abiPreserved s s' ∧
      (inPlaceK Spec.MlDsa.nttInv).post s s' := by
  have hw : pR (s.gpr .x0) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .x1) ∈ s.rd++s.wr := by rw [hs.1,hs.2.1]; simp
  have hrun : WP isa VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv s
      (fun s' => PolyIs s'.mem (s.gpr .x0)
        ((nttInvLens.foldl nttInvLayer (polyAt s.mem (s.gpr .x0))).map (· * 8347681))) := by
    refine WP.seq (WP.mono (pro_ok hs negZetaTab) fun s₁ ⟨hp,ht,hc,_,hk⟩ => ?_)
    refine WP.seq (WP.mono (layers_ok bflyInv false negZetaTab nttInvLayer
      (fun hl => layer_inv_ok hl) nttInvLens
      (by intro l hl; simpa [nttInvLens,nttLens,or_comm,or_left_comm,or_assoc] using hl)
      (hk.get .x0) (hk.get .x1) hc hp ht (by rw [hk.wr]; exact hw)
      (by rw [hk.rd,hk.wr]; exact hz) hs.2.2.1.symm) fun s₂ ⟨hp2,hi⟩ => ?_)
    exact scale_ok (by rw [hi.keep.get .x0,hk.get .x0]) hi.consts hp2
      (by rw [hi.keep.wr,hk.wr]; exact hw)
  obtain ⟨t,s',he,hp⟩ := hrun
  refine ⟨t,s',he,VG.Proof.MlKem.AArch64.abi_of nttInv_noCalls (by lit_decide) he (by lit_decide),?_⟩
  show PolyIs _ _ _
  rw [nttInv_eq_layers]
  exact hp

theorem nttInv_ct : ConstantTime isa (inPlaceK Spec.MlDsa.nttInv).pre (inPlaceK Spec.MlDsa.nttInv).pub
    VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0,.x1])
    VG.Proof.MlDsa.AArch64.Arith.inPlace_agree (by taint_decide)

theorem nttInv_verified : Verified AArch64.target VG.Impl.MlDsa.AArch64.Arith.Neon.nttInv
    (Spec.MlDsa.nttInvContract AArch64.abi) :=
  Verified.of_correct nttInv_correct nttInv_ct (by
    mldsa_implies [Spec.MlDsa.nttInvContract,Spec.MlDsa.inPlaceContract,Spec.MlDsa.inPlaceSig,inPlaceK,
      AArch64.abi,AArch64.argRegs] [VG.Proof.MlDsa.AArch64.Arith.inPlaceSat]
      using VG.Proof.MlDsa.AArch64.Arith.inPlaceSat)
end VG.Proof.MlDsa.AArch64.Arith.Neon
