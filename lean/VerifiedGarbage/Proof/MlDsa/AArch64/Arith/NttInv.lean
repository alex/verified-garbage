import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Ntt

/-!
# ML-DSA on AArch64: `vg_mldsa_inv_ntt`

The butterfly's code does what `bflyInv` does (`bflyInv_spec`), with the
negated zetas of the table (`negZetaTab_of`), so each layer is `nttInvLayer`,
the eight layers are those of `NTT⁻¹` (`nttInv_eq_layers`), and the last loop
multiplies each coefficient by `8347681 = 256⁻¹ mod q`.
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas nttInv)

namespace NttInv

open Ntt (LI)

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ Chain (256 / len - 1 - 128 / len) ls

theorem lens_inv : ∀ len ∈ nttLens, 128 / len + 1 ≤ 256 / len ∧ 256 / len ≤ 256 := by decide

theorem step_down (zP : Addr) (m : Nat) : zstep false (coeffAddr zP (m + 1)) = coeffAddr zP m := by
  rw [zstep, ite_eq_right Bool.false_ne_true, ← coeffAddr_next, BitVec.add_sub_cancel]

theorem negZetaTab_of : TabOf negZetaTab fun k => -zetas k := fun k _ => negZetaNat_eq k

theorem lays_ok {s₀ : State} {fP zP : Addr} (hw : pR fP ∈ s₀.wr) (hz : pR zP ∈ s₀.rd ++ s₀.wr)
    (hd : (pR zP).Disjoint (pR fP)) :
    ∀ (ls : List Nat) (F : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ nttLens) → Chain k ls →
      LI negZetaTab s₀ fP zP F k s →
      WP isa (nttInvLays ls) s fun s' => ∃ k', LI negZetaTab s₀ fP zP (ls.foldl nttInvLayer F) k' s'
  | [], F, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, F, k, s, hls, ⟨hk, hc⟩, hI => by
    have hlen := hls len (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := lens_inv len hlen
    refine WP.seq (WP.mono (lay_ok bflyInv_spec negZetaTab_of hlen false (fun c => 256 / len - 1 - c)
      (fun c hc => by omega)
      (fun c hc => by
        rw [show 256 / len - 1 - c = (256 / len - 1 - (c + 1)) + 1 by omega]
        exact step_down zP _)
      F s hI.x2 (by rw [hI.x3, hk]; rfl) hI.consts hI.poly (by rw [hI.keep.wr]; exact hw)
      (by rw [hI.keep.rd, hI.keep.wr]; exact hz) hd hI.tab) fun s' ⟨⟨hP, hf, hx2, h3⟩, hk'⟩ => ?_)
    exact lays_ok hw hz hd ls _ _ s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf hx2 h3 hk' hd)

theorem chain_inv : Chain 255 nttInvLens := by
  simp only [nttInvLens, Chain]; decide

/-! ## The multiplication by 8347681 -/

theorem scaleBody_ok (s : State) (hc : Consts s) (h : InRegions (s.rd ++ s.wr) (s.gpr .x2) 4)
    (w : InRegions s.wr (s.gpr .x2) 4) :
    WP isa (.block scaleBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x2) ((redX (w64 (s.mem.readW (s.gpr .x2) 32) * s.gpr .x6)).setWidth 32) ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1) ∧
      Keep [.x2, .x5, .x12, .x13] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold scaleBody reduce Impl.MlKem.AArch64.csub
  arun [h, w, hc.x9, hc.x10, hc.x11, redX, csubX]

/-- After `i` coefficients of `G` multiplied by 8347681, from the state `sL`. -/
structure SInv (sL : State) (fP : Addr) (G : Poly) (i : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = coeffAddr fP i
  x6 : s.gpr .x6 = BitVec.ofNat 64 (8347681 : Zq).val
  consts : Consts s
  frame : Frame [pR fP] sL.mem s.mem
  coeff : ∀ k < 256, (coeffAt s.mem fP k).toNat = if k < i then (G[k]! * 8347681).val else (G[k]!).val
  keep : Keep [.x2, .x5, .x6, .x12, .x13] sL s

theorem scale_step {sL : State} {fP : Addr} {G : Poly} (hw : pR fP ∈ sL.wr) {i : Nat} (hi : i < 256)
    {s : State} (hI : SInv sL fP G i s) :
    WP isa (.block scaleBody) s fun s' => SInv sL fP G (i + 1) s' ∧
      s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1 := by
  have hw' : pR fP ∈ s.wr := by rw [hI.keep.wr]; exact hw
  refine WP.mono (scaleBody_ok s hI.consts
    (by rw [hI.x2]; exact ⟨_, List.mem_append_right _ hw', coeff_contains _ hi⟩)
    (by rw [hI.x2]; exact ⟨_, hw', coeff_contains _ hi⟩)) fun s' ⟨⟨hm, hx2, hx5⟩, hk⟩ => ⟨?_, hx5⟩
  have hv : ((redX (w64 (coeffAt s.mem fP i) * s.gpr .x6)).setWidth 32).toNat = (G[i]! * 8347681).val := by
    rw [hI.x6]
    exact redX_mul (x := G[i]!) (by rw [hI.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]) |>.trans
      (by rw [val_mul, val_mul, Nat.mul_comm])
  rw [hI.x2, ← coeffAt_eq] at hm
  refine ⟨by rw [hx2, hI.x2, coeffAddr_next], by rw [hk.get .x6, hI.x6],
    ⟨by rw [hk.get .x9, hI.consts.x9], by rw [hk.get .x10, hI.consts.x10], by rw [hk.get .x11, hI.consts.x11]⟩,
    by rw [hm]; exact hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hi),
    fun k hk' => ?_, (hI.keep.trans hk).mono⟩
  rw [hm, coeffAt_writeW _ _ hk' hi]
  by_cases e : i = k
  · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _)]; exact hv
  · rw [ite_eq_right e, hI.coeff k hk']
    by_cases h : k < i
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem scalePro_ok (s : State) :
    WP isa (.block (movW .x6 (BitVec.ofNat 32 8347681) ++ ([.movz .x .x5 256 0] : List Instr))) s fun s' =>
      (s'.gpr .x6 = BitVec.ofNat 64 (8347681 : Zq).val ∧ s'.gpr .x5 = BitVec.ofNat 64 256 ∧ s'.mem = s.mem) ∧
        Keep [.x6, .x5] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok .x6 _ s) fun s₁ ⟨⟨h6, hm⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x5] (Q := fun s => s.gpr .x5 = BitVec.ofNat 64 256 ∧ s.mem = s₁.mem) (by arun)
    (by decide)) fun s₂ ⟨⟨h5, hm₂⟩, k₂⟩ => ⟨⟨?_, h5, by rw [hm₂, hm]⟩, (k₁.trans k₂).mono⟩
  rw [k₂.get .x6, h6]
  decide

/-- The multiplication of every coefficient by 8347681. -/
theorem scale_ok {fP : Addr} {G : Poly} (sL : State) (hx2 : sL.gpr .x2 = fP) (hc : Consts sL)
    (hG : PolyIs sL.mem fP G) (hw : pR fP ∈ sL.wr) :
    WP isa (.seq (.block (movW .x6 (BitVec.ofNat 32 8347681) ++ ([.movz .x .x5 256 0] : List Instr)))
        (.loop (.block scaleBody) (.nonzero .x .x5))) sL fun s' =>
      PolyIs s'.mem fP (G.map (· * 8347681)) ∧ Frame [pR fP] sL.mem s'.mem ∧
        Keep [.x6, .x5, .x2, .x5, .x6, .x12, .x13] sL s' := by
  refine WP.seq (WP.mono (scalePro_ok sL) fun s3 ⟨⟨h63, h53, hm3⟩, k3⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x5) (N := 256) (by decide) (by decide) (SInv s3 fP G)
    (fun i hi s hI _ => scale_step (by rw [k3.wr]; exact hw) hi hI)
    ⟨by rw [k3.get .x2, hx2, coeffAddr, Nat.mul_zero, BitVec.add_zero], h63,
      ⟨by rw [k3.get .x9, hc.x9], by rw [k3.get .x10, hc.x10], by rw [k3.get .x11, hc.x11]⟩,
      Frame.refl _ _, fun k hk => by rw [ite_eq_right (Nat.not_lt_zero _), hm3]; exact polyIs_toNat hG hk,
      Keep.refl _ _⟩ h53) fun s' hI => ⟨?_, by rw [← hm3]; exact hI.frame, (k3.trans hI.keep).mono⟩
  refine polyIs_of_toNat fun k hk => ?_
  rw [hI.coeff k hk, ite_eq_left hk, map_mul_get _ _ hk]

end NttInv

theorem nttInv_noCalls : Impl.MlDsa.AArch64.Arith.nttInv.noCalls = true := by lit_decide

theorem nttInv_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Arith.nttInv s t s' ∧ abiPreserved s s' ∧
      (inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .x0) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .x1) ∈ s.rd ++ s.wr := by rw [hs.1, hs.2.1]; simp
  obtain ⟨t, s', he, hP⟩ := WP.seq (M := isa) (Q := fun s' =>
      PolyIs s'.mem (s.gpr .x0) (nttInv (polyAt s.mem (s.gpr .x0))))
    (WP.mono (Ntt.pro_ok hs negZetaTab 255 (by decide)) fun s1 hI =>
      WP.seq (WP.mono (NttInv.lays_ok hw hz hs.2.2.1.symm nttInvLens _ 255 s1 (fun _ h => by
        simp only [nttInvLens, nttLens, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)
          NttInv.chain_inv hI) fun s2 ⟨k, hI2⟩ =>
      WP.mono (NttInv.scale_ok s2 hI2.x2 hI2.consts hI2.poly (by rw [hI2.keep.wr]; exact hw))
        fun s' ⟨hP, _, _⟩ => by rw [nttInv_eq_layers]; exact hP))
  exact ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of nttInv_noCalls (by lit_decide) he, hP⟩

theorem nttInv_ct :
    ConstantTime isa (inPlaceK nttInv).pre (inPlaceK nttInv).pub Impl.MlDsa.AArch64.Arith.nttInv :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1]) inPlace_agree (by taint_decide)

theorem nttInv_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Arith.nttInv (Spec.MlDsa.nttInvContract AArch64.abi) :=
  Verified.of_correct nttInv_correct nttInv_ct (by
    mldsa_implies [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      AArch64.abi, AArch64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.AArch64.Arith
