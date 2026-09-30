import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt

/-!
# ML-DSA on x86-64: `vg_mldsa_inv_ntt`

Untrusted: everything here is checked by Lean. The butterfly's code does
what `bflyInv` does (`bflyInv_spec`), with the negated zetas of the table
(`negZetaTab_of`), so each layer is `nttInvLayer`, the eight layers are
those of `NTT⁻¹` (`nttInv_eq_layers`), and the last loop multiplies each
coefficient by `8347681 = 256⁻¹ mod q`.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of wp_counted ifp ifn)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas nttInv)

namespace NttInv

open Ntt (LI)

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ Chain (256 / len - 1 - 128 / len) ls

theorem lens_inv : ∀ len ∈ nttLens, 128 / len + 1 ≤ 256 / len ∧ 256 / len ≤ 256 := by decide

theorem sx_m4 : BitVec.signExtend 64 (-4 : BitVec 32) = -4 := by decide

theorem step_down (zP : Addr) (m : Nat) :
    coeffAddr zP (m + 1) + BitVec.signExtend 64 (-4 : BitVec 32) = coeffAddr zP m := by
  rw [sx_m4, ← coeffAddr_succ, BitVec.add_assoc, show (4 : BitVec 64) + -4 = 0#64 by decide, BitVec.add_zero]

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
    refine WP.seq (WP.mono (lay_ok bflyInv_spec negZetaTab_of hlen (-4) (fun c => 256 / len - 1 - c)
      (fun c hc => by omega)
      (fun c hc => by
        rw [show 256 / len - 1 - c = (256 / len - 1 - (c + 1)) + 1 by omega]
        exact step_down zP _)
      F s hI.rsi (by rw [hI.r8, hk]; rfl) hI.poly (by rw [hI.wr]; exact hw) (by rw [hI.rd, hI.wr]; exact hz) hd
      hI.tab) fun s' ⟨⟨hP, hf, hsi, h8⟩, hk'⟩ => ?_)
    exact lays_ok hw hz hd ls _ _ s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf hsi h8 hk' hd)

theorem chain_inv : Chain 255 nttInvLens := by
  simp only [nttInvLens, Chain]; decide

/-! ## The multiplication by 8347681 -/

theorem scaleHead_ok (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4) :
    WP isa (.block ([.mov32 .rax (.mem (at_ .rsi 0)), .mul .r9] : List Instr)) s fun s' =>
      (s'.gpr .rax = prodW (s.mem.readW (s.gpr .rsi) 32) (s.gpr .r9) ∧ s'.mem = s.mem) ∧
        Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrund [h]

theorem scaleBody_ok (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4) (w : InRegions s.wr (s.gpr .rsi) 4) :
    WP isa (.block scaleBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rsi) (BitVec.setWidth 32 (redD (prodW (s.mem.readW (s.gpr .rsi) 32)
          (s.gpr .r9)))) ∧ s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rsi, .rcx, .r10, .r11] s s' := by
  unfold scaleBody
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (scaleHead_ok s h) fun s1 ⟨⟨ha, hm1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s1) fun s2 ⟨⟨hr, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hsi : s2.gpr .rsi = s.gpr .rsi := k12.gpr (by decide)
  have hcx : s2.gpr .rcx = s.gpr .rcx := k12.gpr (by decide)
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun s' => s'.mem = s2.mem.writeW (s2.gpr .rsi)
      (BitVec.setWidth 32 (s2.gpr .r10)) ∧ s'.gpr .rsi = s2.gpr .rsi + 4 ∧ s'.gpr .rcx = s2.gpr .rcx - 1 ∧
      s'.zf = some (s2.gpr .rcx - 1 == 0)) (by
        xrund [show InRegions s2.wr (s2.gpr .rsi) 4 by rw [k12.2.2, hsi]; exact w])
      (by decide)) fun s3 ⟨⟨hm3, h3si, h3cx, h3z⟩, k3⟩ => ⟨?_, (k12.trans k3).mono (by decide)⟩
  rw [hm3, h3si, h3cx, h3z, hcx, hsi, hr, hm2, hm1, ha]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- After `i` coefficients of `G` multiplied by 8347681, from the state `sL`. -/
structure SInv (sL : State) (fP : Addr) (G : Poly) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = coeffAddr fP i
  r9 : s.gpr .r9 = BitVec.ofNat 64 (8347681 : Zq).val
  rd : s.rd = sL.rd
  wr : s.wr = sL.wr
  frame : Frame [pR fP] sL.mem s.mem
  coeff : ∀ k < 256, (coeffAt s.mem fP k).toNat = if k < i then (G[k]! * 8347681).val else (G[k]!).val
  keep : Keep [.r9, .rcx, .rax, .rdx, .rsi, .rcx, .r10, .r11] sL s

theorem scale_step {sL : State} {fP : Addr} {G : Poly} (hw : pR fP ∈ sL.wr) {i : Nat} (hi : i < 256)
    {s : State} (hI : SInv sL fP G i s) :
    WP isa (.block scaleBody) s fun s' => SInv sL fP G (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hw' : pR fP ∈ s.wr := by rw [hI.wr]; exact hw
  refine WP.mono (scaleBody_ok s (by rw [hI.rsi]; exact ⟨_, List.mem_append_right _ hw', coeff_contains _ hi⟩)
    (by rw [hI.rsi]; exact ⟨_, hw', coeff_contains _ hi⟩)) fun s' ⟨⟨hm, hsi, hcx, hz⟩, hk⟩ => ⟨?_, hcx, hz⟩
  have hv : (BitVec.setWidth 32 (redD (prodW (coeffAt s.mem fP i) (s.gpr .r9)))).toNat =
      (G[i]! * 8347681).val := by
    rw [hI.r9, redD_prodW (x := G[i]!) (by rw [hI.coeff i hi, ifn (Nat.lt_irrefl i)]), val_mul, val_mul,
      Nat.mul_comm]
  rw [hI.rsi, ← coeffAt_eq] at hm
  refine ⟨by rw [hsi, hI.rsi, coeffAddr_succ], by rw [hk.gpr (by decide), hI.r9], hk.2.1.trans hI.rd,
    hk.2.2.trans hI.wr, by rw [hm]; exact hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hi),
    fun k hk' => ?_, (hI.keep.trans hk).mono (by decide)⟩
  rw [hm, coeffAt_writeW _ _ hk' hi]
  by_cases e : i = k
  · subst e; rw [ifp rfl, ifp (Nat.lt_succ_self _)]; exact hv
  · rw [ifn e, hI.coeff k hk']
    by_cases h : k < i
    · rw [ifp h, ifp (by omega)]
    · rw [ifn h, ifn (by omega)]

/-- The multiplication of every coefficient by 8347681. -/
theorem scale_ok {fP : Addr} {G : Poly} (sL : State) (hsi : sL.gpr .rsi = fP) (hG : PolyIs sL.mem fP G)
    (hw : pR fP ∈ sL.wr) :
    WP isa (.seq (.block [.mov32 .r9 (.imm 8347681)])
        (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block scaleBody) .ne))) sL fun s' =>
      PolyIs s'.mem fP (G.map (· * 8347681)) ∧ Frame [pR fP] sL.mem s'.mem ∧
        Keep [.r9, .rcx, .rax, .rdx, .rsi, .rcx, .r10, .r11] sL s' := by
  refine WP.seq (WP.mono (WP.keep [.r9]
      (Q := fun s => s.mem = sL.mem ∧ s.gpr .r9 = BitVec.ofNat 64 (8347681 : Zq).val)
      (by xrund) (by decide)) fun s3 ⟨⟨hm3, h93⟩, k3⟩ => ?_)
  refine WP.mono (wp_counted (s₀ := s3) (N := 256) (v := 256) rfl (by decide) (SInv sL fP G)
    (fun s4 hm4 hk4 => ⟨by rw [hk4.gpr (by decide), k3.gpr (by decide), hsi]; simp,
      by rw [hk4.gpr (by decide), h93], hk4.2.1.trans k3.2.1, hk4.2.2.trans k3.2.2,
      by rw [hm4, hm3]; exact Frame.refl _ _,
      fun k hk => by rw [ifn (Nat.not_lt_zero _), hm4, hm3]; exact polyIs_toNat hG hk,
      (k3.trans hk4).mono (by decide)⟩)
    fun i hi s hI => scale_step hw hi hI) fun s' hI => ⟨?_, hI.frame, hI.keep⟩
  refine polyIs_of_toNat fun k hk => ?_
  rw [hI.coeff k hk, ifp hk, map_mul_get _ _ hk]

end NttInv

theorem nttInv_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.nttInv s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hs.1, hs.2.1]; simp
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Arith.nttInv)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
    (Q := fun s' => PolyIs s'.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem)
    (WP.seq (WP.mono (Ntt.pro_ok hs negZetaTab (4 * 255) 255 (by decide)) fun s1 hI =>
      WP.seq (WP.mono (NttInv.lays_ok hw hz hs.2.2.1.symm nttInvLens _ 255 s1 (fun _ h => by
        simp only [nttInvLens, nttLens, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)
          NttInv.chain_inv hI) fun s2 ⟨k, hI2⟩ =>
      WP.mono (NttInv.scale_ok s2 hI2.rsi hI2.poly (by rw [hI2.wr]; exact hw)) fun s' ⟨hP, hf, _⟩ =>
        ⟨by rw [nttInv_eq_layers]; exact hP, hI2.frame.trans (hf.mono (by simp))⟩))) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), hP⟩

theorem nttInv_ct : ConstantTime isa (inPlaceK nttInv).pre (inPlaceK nttInv).pub Impl.MlDsa.X86_64.Arith.nttInv :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

theorem nttInv_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.nttInv (Spec.MlDsa.nttInvContract X86_64.abi) :=
  Verified.of_correct nttInv_correct nttInv_ct (by
    mldsa_implies [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith
