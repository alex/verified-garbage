import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: `vg_mlkem_ntt`

`withMxcsr` runs its code from any MXCSR and keeps what it does
(`withMxcsr_ok`); the prologue leaves the table of zetas and `f` as words in
`scratch` (`vpro_ok`), each layer is `nttLayer` (`vlay_ok`, `vlay4_ok`,
`vlay2_ok`), and the seven layers are `NTT` (`ntt_eq_layers`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `vg_mlkem_ntt(f = rdi, scratch = rsi)` and `vg_mlkem_inv_ntt`: `f`
becomes `t f`. -/
def inPlaceK (t : Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## The prologue and the epilogue -/

/-- The table of zetas at `scratch`, `f` as words in `S`, and the constants. -/
theorem vpro_ok {fP sP : Addr} {F : Poly} {s : State} (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hF : PolyIs s.mem fP F) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) (hd : (pR fP).Disjoint (pR sP)) :
    WP isa vpro s fun s' => S16 s'.mem (spW sP) F ∧ T16 s'.mem sP ∧ VConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.rax, .rcx, .rdx, .r9] s s' := by
  simp only [vpro, List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (wordTab_ok hsi hw) fun s1 ⟨hT, hf1, k1, _, _⟩ => ?_
  have hsi1 : s1.gpr .rsi = sP := by rw [k1.gpr (by decide), hsi]
  have hdi1 : s1.gpr .rdi = fP := by rw [k1.gpr (by decide), hdi]
  refine WP.mono (Q := fun (s2 : State) => VConsts s2 ∧ s2.gpr .r9 = fP ∧ s2.gpr .rdx = spW sP ∧
      s2.mem = s1.mem ∧ Keep [.rax, .r9, .rdx] s1 s2)
    (by
      simp only [vconsts, leaR, oS]
      vrunm [hsi1, hdi1, sx_ofNat (show 256 < 2 ^ 31 by decide)]
      refine ⟨⟨?_, ?_⟩, ⟨fun r hr => ?_, rfl, rfl⟩⟩
      · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, ite_true]; decide
      · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, ite_true, ite_false,
          reduceCtorEq]; decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_setXmm, hr, ite_false]) fun s2 ⟨hc, h9, hdx, hm2, k2⟩ => ?_
  have k12 := k1.trans k2
  have hF2 : PolyIs s2.mem fP F := by
    rw [hm2]
    exact polyIs_frame hf1 (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (pR_sub_tab sP)) hF
  have hwf2 : pR fP ∈ s2.rd ++ s2.wr := by rw [k12.2.2]; exact List.mem_append_right _ hwf
  have hw2 : pR sP ∈ s2.wr := by rw [k12.2.2]; exact hw
  refine WP.mono (vpack_ok hc hF2 h9 hdx hwf2 hw2 hd) fun s3 ⟨hS, hf3, hc3, k3, _⟩ =>
    ⟨hS, (hm2 ▸ hT).frame hf3, hc3, ?_, (k12.trans k3).mono (by simp)⟩
  refine (hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
    (hm2 ▸ hf3.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
  · rw [List.mem_singleton.mp hr]; exact pR_sub_tab sP
  · rw [List.mem_singleton.mp hr]; exact pR_sub_S sP

/-- `S` unpacked into `f`. -/
theorem vepi_ok {fP sP : Addr} {F : Poly} {s : State} (hc : VConsts s) (hS : S16 s.mem (spW sP) F)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa vepi s fun s' => PolyIs s'.mem fP F ∧ Frame [pR fP] s.mem s'.mem ∧ Keep [.rcx, .rdx, .r9] s s' := by
  simp only [vepi]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r9 = fP ∧ s1.gpr .rdx = spW sP ∧
      s1.mem = s.mem ∧ s1.xmm = s.xmm ∧ Keep [.r9, .rdx] s s1)
    (by
      simp only [leaR, oS]
      vrunm [hsi, hdi, sx_ofNat (show 256 < 2 ^ 31 by decide)]
      refine ⟨fun r hr => ?_, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h9, hdx, hm, hx, k1⟩ => ?_)
  have hc1 : VConsts s1 := ⟨by rw [hx]; exact hc.q, by rw [hx]; exact hc.qinv⟩
  refine WP.mono (vunpack_ok hc1 (by rw [hm]; exact hS) h9 hdx (by rw [k1.2.2]; exact hwf)
    (by rw [k1.2.2]; exact hw) hd) fun s2 ⟨hP, hf, _, k2, _⟩ =>
      ⟨hP, hm ▸ hf, (k1.trans k2).mono (by decide)⟩

/-! ## The layers -/

/-- Between the layers: `S` holds `F`, and the table and the constants are
in place. -/
structure LI (sP : Addr) (s₀ : State) (F : Poly) (s : State) : Prop where
  S : S16 s.mem (spW sP) F
  T : T16 s.mem sP
  c : VConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [sR (spW sP)] s₀.mem s.mem

/-- A layer, then `c`. -/
theorem LI.seq {sP : Addr} {s₀ : State} (hsi : s₀.gpr .rsi = sP) (hw : pR sP ∈ s₀.wr) {l c : Prog isa}
    {F F' : Poly} {Q : State → Prop}
    (hl : ∀ s, VConsts s → s.gpr .rsi = sP → S16 s.mem (spW sP) F → T16 s.mem sP → pR sP ∈ s.wr →
      WP isa l s fun s' => S16 s'.mem (spW sP) F' ∧ BInv sP s s')
    (hc : ∀ s, LI sP s₀ F' s → WP isa c s Q) {s : State} (hI : LI sP s₀ F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hsi]) hI.S hI.T (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame, hb.consts,
      (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

theorem wAddr_fwd (p : Addr) (a d : Nat) {dz : BitVec 32}
    (h : BitVec.signExtend 64 dz = BitVec.ofNat 64 (2 * d)) :
    wAddr p a + BitVec.signExtend 64 dz = wAddr p (a + d) := by
  rw [h, wAddr_add]

theorem wAddr_bwd (p : Addr) (a d : Nat) {dz : BitVec 32}
    (h : BitVec.ofNat 64 (2 * d) + BitVec.signExtend 64 dz = 0) :
    wAddr p (a + d) + BitVec.signExtend 64 dz = wAddr p a := by
  rw [← wAddr_add, BitVec.add_assoc, h]; exact BitVec.add_zero _

/-- A step of `wAddr` at a zeta index going up by `d`. -/
theorem step_fwd (p : Addr) {zi : Nat → Nat} (d : Nat) {dz : BitVec 32}
    (h : BitVec.signExtend 64 dz = BitVec.ofNat 64 (2 * d)) (hz : ∀ c, zi (c + 1) = zi c + d) (c : Nat) :
    wAddr p (zi c) + BitVec.signExtend 64 dz = wAddr p (zi (c + 1)) := by
  rw [wAddr_fwd p _ d h, hz]

/-- A step of `wAddr` at a zeta index going down by `d`. -/
theorem step_bwd (p : Addr) {zi : Nat → Nat} (d : Nat) {dz : BitVec 32}
    (h : BitVec.ofNat 64 (2 * d) + BitVec.signExtend 64 dz = 0) {c : Nat} (hz : zi c = zi (c + 1) + d) :
    wAddr p (zi c) + BitVec.signExtend 64 dz = wAddr p (zi (c + 1)) := by
  rw [hz, wAddr_bwd p _ d h]

theorem nttLayer_eq (F : Poly) (len : Nat) :
    nttLayer F len = layF nttBlockN F len (fun c => 128 / len + c) (128 / len) := rfl

/-- A layer of `NTT` with `len ≥ 8`, whose first zeta is `zeta k`. -/
theorem fwdLay_ok {sP : Addr} (len k : Nat) (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 128 / len = k)
    {F : Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay vbfly len k 2) s fun s' => S16 s'.mem (spW sP) (nttLayer F len) ∧ BInv sP s s' := by
  rw [nttLayer_eq]
  exact vlay_ok vbfly_spec nttBlk_ok hlen 2 (fun c => 128 / len + c) (by rw [hk]; rfl)
    (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      rcases hlen with rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun c _ => step_fwd (zi := fun c => 128 / len + c) (dz := 2) _ 1 (by decide) (fun _ => by omega) c)
    hc hsi hS hT hw

theorem fwdLay4_ok {sP : Addr} {F : Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay4 vbfly 32 0x50 4) s fun s' => S16 s'.mem (spW sP) (nttLayer F 4) ∧ BInv sP s s' := by
  rw [nttLayer_eq, show 128 / 4 = 32 from rfl]
  exact vlay4_ok vbfly_spec nttBlk_ok 32 0x50 4 (fun c => 32 + c) (fun i => 32 + 2 * i) rfl (by decide)
    (by decide) (fun i _ => step_fwd (zi := fun i => 32 + 2 * i) (dz := 4) _ 2 (by decide) (fun _ => by omega) i)
    hc hsi hS hT hw

theorem fwdLay2_ok {sP : Addr} {F : Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 vbfly 64 0xE4 8) s fun s' => S16 s'.mem (spW sP) (nttLayer F 2) ∧ BInv sP s s' := by
  rw [nttLayer_eq, show 128 / 2 = 64 from rfl]
  exact vlay2_ok vbfly_spec nttBlk_ok 64 0xE4 8 (fun c => 64 + c) (fun i => 64 + 4 * i) rfl (by decide)
    (by decide) (fun i _ => step_fwd (zi := fun i => 64 + 4 * i) (dz := 8) _ 4 (by decide) (fun _ => by omega) i)
    hc hsi hS hT hw

theorem ntt_correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.ntt s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa Impl.MlKem.X86_64.ntt s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold Impl.MlKem.X86_64.ntt
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw ?_ fun s1 k1 f1 => ?_
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
    refine LI.seq hsi2 hw2 (fwdLay_ok 128 1 (by decide) (by decide)) ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LI.seq hsi2 hw2 (fwdLay_ok 64 2 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fwdLay_ok 32 4 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fwdLay_ok 16 8 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fwdLay_ok 8 16 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 fwdLay4_ok ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 fwdLay2_ok ?_ hI
    intro s3 hI
    refine WP.mono (vepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4, _⟩ => ⟨?_, ?_⟩
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

theorem ntt_ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub Impl.MlKem.X86_64.ntt :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def inPlaceSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified X86_64.target Impl.MlKem.X86_64.ntt (Spec.MlKem.nttContract X86_64.abi) :=
  Verified.of_correct ntt_correct ntt_ct (by
    mlkem_implies [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlKem.X86_64
