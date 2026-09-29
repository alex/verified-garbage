import VerifiedGarbage.Proof.MlKem.X86_64.Ntt

/-!
# ML-KEM on x86-64: `vg_mlkem_inv_ntt`

Untrusted: everything here is checked by Lean. The butterfly's code does
what `bflyInv` does (`bflyInv_spec`), so each layer is `nttInvLayer`, the
seven layers are those of `NTT⁻¹` (`nttInv_eq_layers`), and the last loop
multiplies each coefficient by 3303.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem bflyInv_spec : BflyOk Impl.MlKem.X86_64.bflyInv MlKem.bflyInv := by
  intro fP len j hlen hj z F s hsi h9 hF hw
  obtain ⟨r0, r1, w0, w1⟩ := bfly_regions hj hsi hw
  refine WP.mono (bflyInv_ok len s r0 r1 w0 w1) fun s' ⟨⟨hm, hsi', hcx, hz⟩, hk⟩ => ⟨⟨?_, ?_, hsi', hcx, hz⟩, hk⟩
  · rw [hm, h9, hsi, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq]
    have hj' : j < 256 := by omega
    have ha := polyIs_toNat hF hj'
    have hu := polyIs_toNat hF hj
    have hne : j ≠ j + len := by omega
    show PolyIs _ _ ((F.set! j (F[j]! + F[j + len]!)).set! (j + len)
      (z * ((F.set! j (F[j]! + F[j + len]!))[j + len]! - F[j]!)))
    rw [getElem!_set!_ne _ hj hne]
    have hd : (csub32 (coeffAt s.mem fP (j + len) + qImm - coeffAt s.mem fP j)).toNat = (F[j + len]! - F[j]!).val := by
      rw [csub32_sub (by rw [hu]; exact val_lt _) (by rw [ha]; exact val_lt _), ha, hu, val_sub]
    refine polyIs_writeW' (polyIs_writeW' hF hj' _ ?_) hj _ (mulz_toNat hd)
    rw [csub32_add (by rw [ha]; exact val_lt _) (by rw [hu]; exact val_lt _), ha, hu, val_add]
  · rw [hm, hsi, coeffAddr_add]
    exact (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show j < 256 by omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)

namespace NttInv

open Ntt (LI)

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ Chain (256 / len - 1 - 128 / len) ls

theorem lens_inv : ∀ len ∈ nttLens, 128 / len + 1 ≤ 256 / len ∧ 256 / len ≤ 128 := by decide

theorem sx_m4 : BitVec.signExtend 64 (-4 : BitVec 32) = -4 := by decide

theorem step_down (zP : Addr) (m : Nat) : coeffAddr zP (m + 1) + BitVec.signExtend 64 (-4 : BitVec 32) = coeffAddr zP m := by
  rw [sx_m4, ← coeffAddr_succ, BitVec.add_assoc, show (4 : BitVec 64) + -4 = 0#64 by decide, BitVec.add_zero]

theorem lays_ok {s₀ : State} {fP zP : Addr} (hw : pR fP ∈ s₀.wr) (hz : pR zP ∈ s₀.rd ++ s₀.wr)
    (hd : (pR zP).Disjoint (pR fP)) :
    ∀ (ls : List Nat) (F : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ nttLens) → Chain k ls →
      LI s₀ fP zP F k s →
      WP isa (nttInvLays ls) s fun s' => ∃ k', LI s₀ fP zP (ls.foldl nttInvLayer F) k' s'
  | [], F, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, F, k, s, hls, ⟨hk, hc⟩, hI => by
    have hlen := hls len (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := lens_inv len hlen
    refine WP.seq (WP.mono (lay_ok bflyInv_spec hlen (-4) (fun c => 256 / len - 1 - c) (fun c hc => by omega)
      (fun c hc => by
        rw [show 256 / len - 1 - c = (256 / len - 1 - (c + 1)) + 1 by omega]
        exact step_down zP _)
      F s hI.rsi (by rw [hI.r8, hk]; rfl) hI.poly (by rw [hI.wr]; exact hw) (by rw [hI.rd, hI.wr]; exact hz) hd
      hI.tab) fun s' ⟨⟨hP, hf, hsi, h8⟩, hk'⟩ => ?_)
    exact lays_ok hw hz hd ls _ _ s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf hsi h8 hk' hd)

theorem chain_inv : Chain 127 nttInvLens := by
  simp only [nttInvLens, Chain]; decide

/-! ## The multiplication by 3303 -/

theorem scaleHead_ok (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4) :
    WP isa (.block ([.mov32 .rax (.mem (at_ .rsi 0)), .mul .r9] : List Instr)) s fun s' =>
      (s'.gpr .rax = prodR9 (s.mem.readW (s.gpr .rsi) 32) (s.gpr .r9) ∧ s'.mem = s.mem) ∧
        Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h]

theorem scaleBody_ok (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4) (w : InRegions s.wr (s.gpr .rsi) 4) :
    WP isa (.block scaleBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rsi) (BitVec.setWidth 32 (redV (prodR9 (s.mem.readW (s.gpr .rsi) 32)
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
        xrun [show InRegions s2.wr (s2.gpr .rsi) 4 by rw [k12.2.2, hsi]; exact w])
      (by decide)) fun s3 ⟨⟨hm3, h3si, h3cx, h3z⟩, k3⟩ => ⟨?_, (k12.trans k3).mono (by decide)⟩
  rw [hm3, h3si, h3cx, h3z, hcx, hsi, hr, hm2, hm1, ha]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- After `i` coefficients of `G` multiplied by 3303, from the state `sL`. -/
structure SInv (sL : State) (fP : Addr) (G : Poly) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = coeffAddr fP i
  r9 : s.gpr .r9 = BitVec.ofNat 64 (3303 : Zq).val
  rd : s.rd = sL.rd
  wr : s.wr = sL.wr
  frame : Frame [pR fP] sL.mem s.mem
  coeff : ∀ k < 256, (coeffAt s.mem fP k).toNat = if k < i then (G[k]! * 3303).val else (G[k]!).val
  keep : Keep [.r9, .rcx, .rax, .rdx, .rsi, .rcx, .r10, .r11] sL s

theorem scale_step {sL : State} {fP : Addr} {G : Poly} (hw : pR fP ∈ sL.wr) {i : Nat} (hi : i < 256)
    {s : State} (hI : SInv sL fP G i s) :
    WP isa (.block scaleBody) s fun s' => SInv sL fP G (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hw' : pR fP ∈ s.wr := by rw [hI.wr]; exact hw
  refine WP.mono (scaleBody_ok s (by rw [hI.rsi]; exact ⟨_, List.mem_append_right _ hw', coeff_contains _ hi⟩)
    (by rw [hI.rsi]; exact ⟨_, hw', coeff_contains _ hi⟩)) fun s' ⟨⟨hm, hsi, hcx, hz⟩, hk⟩ => ⟨?_, hcx, hz⟩
  have hv : (BitVec.setWidth 32 (redV (prodR9 (coeffAt s.mem fP i) (s.gpr .r9)))).toNat = (G[i]! * 3303).val := by
    rw [hI.r9, mulz_toNat (x := G[i]!) (by rw [hI.coeff i hi, ifn (Nat.lt_irrefl i)]), val_mul, val_mul,
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

/-- The multiplication of every coefficient by 3303. -/
theorem scale_ok {fP : Addr} {G : Poly} (sL : State) (hsi : sL.gpr .rsi = fP) (hG : PolyIs sL.mem fP G)
    (hw : pR fP ∈ sL.wr) :
    WP isa (.seq (.block [.mov32 .r9 (.imm 3303)])
        (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block scaleBody) .ne))) sL fun s' =>
      PolyIs s'.mem fP (G.map (· * 3303)) ∧ Frame [pR fP] sL.mem s'.mem ∧
        Keep [.r9, .rcx, .rax, .rdx, .rsi, .rcx, .r10, .r11] sL s' := by
  refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun s => s.mem = sL.mem ∧ s.gpr .r9 = BitVec.ofNat 64 (3303 : Zq).val)
      (by xrun) (by decide)) fun s3 ⟨⟨hm3, h93⟩, k3⟩ => ?_)
  refine WP.mono (wp_counted (s₀ := s3) (N := 256) (v := 256) rfl (by decide) (SInv sL fP G)
    (fun s4 hm4 hk4 => ⟨by rw [hk4.gpr (by decide), k3.gpr (by decide), hsi]; simp,
      by rw [hk4.gpr (by decide), h93], hk4.2.1.trans k3.2.1, hk4.2.2.trans k3.2.2,
      by rw [hm4, hm3]; exact Frame.refl _ _,
      fun k hk => by rw [ifn (Nat.not_lt_zero _), hm4, hm3]; exact polyIs_toNat hG hk,
      (k3.trans hk4).mono (by decide)⟩)
    fun i hi s hI => scale_step hw hi hI) fun s' hI => ⟨?_, hI.frame, hI.keep⟩
  refine polyIs_of_toNat fun k hk => ?_
  rw [hI.coeff k hk, ifp hk, map_mul_get _ hk]

end NttInv

theorem nttInv_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.nttInv s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hs.1, hs.2.1]; simp
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep (c := Impl.MlKem.X86_64.nttInv)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
    (Q := fun s' => PolyIs s'.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem)
    (WP.seq (WP.mono (Ntt.pro_ok hs (4 * 127) 127 (by decide)) fun s1 hI =>
      WP.seq (WP.mono (NttInv.lays_ok hw hz hs.2.2.1.symm nttInvLens _ 127 s1 (fun _ h => by
        simp only [nttInvLens, nttLens, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)
          NttInv.chain_inv hI) fun s2 ⟨k, hI2⟩ =>
      WP.mono (NttInv.scale_ok s2 hI2.rsi hI2.poly (by rw [hI2.wr]; exact hw)) fun s' ⟨hP, hf, _⟩ =>
        ⟨by rw [nttInv_eq_layers]; exact hP, hI2.frame.trans (hf.mono (by simp))⟩))) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), hP⟩

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
