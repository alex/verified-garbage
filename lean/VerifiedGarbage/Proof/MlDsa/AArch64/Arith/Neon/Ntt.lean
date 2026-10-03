import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Ntt

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (inPlaceK Tab)
open VG.Spec.MlDsa (Poly PolyIs polyAt)

theorem layers_ok (bf : List Instr) (up : Bool) (tab : Nat → Nat) (step : Poly → Nat → Poly)
    (hstep : ∀ {fP zP : Addr} {len : Nat}, len ∈ nttLens → ∀ {F : Poly} {s : State},
      s.gpr .x0 = fP → s.gpr .x1 = zP → VConsts s → PolyIs s.mem fP F → Tab tab s.mem zP 256 →
      pR fP ∈ s.wr → pR zP ∈ s.rd++s.wr → (pR zP).Disjoint (pR fP) →
      WP isa (layer bf len up) s (fun s' => PolyIs s'.mem fP (step F len) ∧ BInv fP s s')) :
    ∀ (ls : List Nat), (∀ len ∈ ls, len ∈ nttLens) → ∀ {fP zP : Addr} {F : Poly} {s : State},
      s.gpr .x0 = fP → s.gpr .x1 = zP → VConsts s → PolyIs s.mem fP F → Tab tab s.mem zP 256 →
      pR fP ∈ s.wr → pR zP ∈ s.rd++s.wr → (pR zP).Disjoint (pR fP) →
      WP isa (layers bf up ls) s (fun s' => PolyIs s'.mem fP (ls.foldl step F) ∧ BInv fP s s')
  | [], _, _, _, _, _, _, _, hc, hp, _, _, _, _ => WP.block_nil ⟨hp,BInv.refl hc⟩
  | len::ls, hls, _, _, _, _, h0, h1, hc, hp, ht, hw, hz, hd => by
    refine WP.seq (WP.mono (hstep (hls len (by simp)) h0 h1 hc hp ht hw hz hd)
      fun s₁ ⟨hp1,hi⟩ => ?_)
    exact WP.mono (layers_ok bf up tab step hstep ls (fun l hl => hls l (List.mem_cons_of_mem _ hl))
      (by rw [hi.keep.get .x0,h0]) (by rw [hi.keep.get .x1,h1]) hi.consts hp1
      (ht.frame hi.frame (by simpa using hd) (by decide))
      (by rw [hi.keep.wr]; exact hw) (by rw [hi.keep.rd,hi.keep.wr]; exact hz) hd)
      fun _ ⟨hp2,hi2⟩ => ⟨hp2,hi.trans hi2⟩

theorem ntt_noCalls : VG.Impl.MlDsa.AArch64.Arith.Neon.ntt.noCalls = true := by lit_decide

theorem ntt_correct (s : State) (hs : (inPlaceK Spec.MlDsa.ntt).pre s) :
    ∃ t s', Exec isa VG.Impl.MlDsa.AArch64.Arith.Neon.ntt s t s' ∧ abiPreserved s s' ∧
      (inPlaceK Spec.MlDsa.ntt).post s s' := by
  have hw : pR (s.gpr .x0) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .x1) ∈ s.rd++s.wr := by rw [hs.1,hs.2.1]; simp
  have hrun : WP isa VG.Impl.MlDsa.AArch64.Arith.Neon.ntt s
      (fun s' => PolyIs s'.mem (s.gpr .x0) (nttLens.foldl nttLayer (polyAt s.mem (s.gpr .x0)))) := by
    refine WP.seq (WP.mono (pro_ok hs zetaTab)
      fun s₁ ⟨hp,ht,hc,_,hk⟩ => WP.mono (layers_ok bfly true zetaTab nttLayer
      (fun hl => layer_fwd_ok hl) nttLens (fun _ h => h)
      (hk.get .x0) (hk.get .x1) hc hp ht (by rw [hk.wr]; exact hw)
      (by rw [hk.rd,hk.wr]; exact hz) hs.2.2.1.symm) (fun _ h => h.1))
  obtain ⟨t,s',he,hp⟩ := hrun
  refine ⟨t,s',he,VG.Proof.MlKem.AArch64.abi_of ntt_noCalls (by lit_decide) he (by lit_decide),?_⟩
  show PolyIs _ _ _
  rw [ntt_eq_layers]
  exact hp

theorem ntt_ct : ConstantTime isa (inPlaceK Spec.MlDsa.ntt).pre (inPlaceK Spec.MlDsa.ntt).pub
    VG.Impl.MlDsa.AArch64.Arith.Neon.ntt :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0,.x1])
    VG.Proof.MlDsa.AArch64.Arith.inPlace_agree (by taint_decide)

theorem ntt_verified : Verified AArch64.target VG.Impl.MlDsa.AArch64.Arith.Neon.ntt
    (Spec.MlDsa.nttContract AArch64.abi) :=
  Verified.of_correct ntt_correct ntt_ct (by
    mldsa_implies [Spec.MlDsa.nttContract,Spec.MlDsa.inPlaceContract,Spec.MlDsa.inPlaceSig,inPlaceK,
      AArch64.abi,AArch64.argRegs] [VG.Proof.MlDsa.AArch64.Arith.inPlaceSat]
      using VG.Proof.MlDsa.AArch64.Arith.inPlaceSat)
end VG.Proof.MlDsa.AArch64.Arith.Neon
