import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt

/-!
# ML-DSA on x86-64: `vg_mldsa_inv_ntt`

As `vg_mldsa_ntt` (`Ntt.lean`): each layer is `nttInvLayer` (with `vibfly`,
which multiplies by `ζ` the difference the other way round: `nttInvBlk_ok`),
the eight layers are those of `NTT⁻¹` (`nttInv_eq_layers`), and the last pass
multiplies each coefficient by `8347681 = 256⁻¹ mod q` (`vscale_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly xmm_setXmm ifp ifn sel GOnly wp_rcxLoop add_ofNat_zero)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas nttInv)

/-! ## The layers -/

/-- The block of `NTT⁻¹`. -/
abbrev invBlk : Poly → Nat → Nat → Nat → Nat → Poly := fun f len k st t => blockN bflyInv f len (-zetas k) st t

theorem nttInvLayer_eq (F : Poly) (len : Nat) :
    nttInvLayer F len = layF invBlk F len (fun c => 256 / len - 1 - c) (128 / len) := rfl

/-- A layer of `NTT⁻¹` with `len ≥ 4`, whose first zeta is `zetas k`. -/
theorem invLay_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) (len k : Nat)
    (hlen : len ∈ [4, 8, 16, 32, 64, 128]) (hk : 256 / len - 1 = k)
    {F : Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (vlay vibfly len k (-4)) s fun s' => PolyIs s'.mem fP (nttInvLayer F len) ∧ BInv fP s s' := by
  have hl : 128 / len ≥ 1 ∧ 256 / len = 2 * (128 / len) ∧ 256 / len ≤ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [nttInvLayer_eq]
  exact vlay_ok vibfly_spec nttInvBlk_ok hlen (-4) (fun c => 256 / len - 1 - c) (by rw [hk]; rfl)
    (fun c _ => by omega)
    (fun c hc' => (congrArg (· + _) (congrArg (coeffAddr sP) (show 256 / len - 1 - c =
      256 / len - 1 - (c + 1) + 1 by omega))).trans (step_bwd _ _ 1 (by decide)))
    hc hdi hsi hS hT hwf hw hd

theorem invLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : VConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 vibfly 126 0x05 (-8)) s fun s' => PolyIs s'.mem fP (nttInvLayer F 2) ∧ BInv fP s s' := by
  have hs : ∀ e < 4, sel 0x05 e = 1 - e / 2 := by decide
  rw [nttInvLayer_eq, show 256 / 2 - 1 = 127 from rfl, show 128 / 2 = 64 from rfl]
  exact vlay2_ok vibfly_spec nttInvBlk_ok 126 0x05 (-8) (fun c => 127 - c) (fun i => 126 - 2 * i) rfl
    (fun i _ => by omega) (fun i hi e he => by rw [hs e he]; omega)
    (fun i hi => (congrArg (· + _) (congrArg (coeffAddr sP) (show 126 - 2 * i = 126 - 2 * (i + 1) + 2 by
      omega))).trans (step_bwd _ _ 2 (by decide))) hc hdi hsi hS hT hwf hw hd

theorem invLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : VConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (vlay1 vibfly 252 0x1B (-16)) s fun s' => PolyIs s'.mem fP (nttInvLayer F 1) ∧ BInv fP s s' := by
  have hs : ∀ e < 4, sel 0x1B e = 3 - e := by decide
  rw [nttInvLayer_eq, show 256 / 1 - 1 = 255 from rfl, show 128 / 1 = 128 from rfl]
  exact vlay1_ok vibfly_spec nttInvBlk_ok 252 0x1B (-16) (fun c => 255 - c) (fun i => 252 - 4 * i) rfl
    (fun i _ => by omega) (fun i hi e he => by rw [hs e he]; omega)
    (fun i hi => (congrArg (· + _) (congrArg (coeffAddr sP) (show 252 - 4 * i = 252 - 4 * (i + 1) + 4 by
      omega))).trans (step_bwd _ _ 4 (by decide))) hc hdi hsi hS hT hwf hw hd

/-! ## The multiplication by `256⁻¹` -/

/-- The coefficients of `G` before `4i` multiplied by `8347681`. -/
def Scaled (m : Mem) (fP : Addr) (G : Poly) (i : Nat) : Prop :=
  ∀ k < 256, (coeffAt m fP k).toNat = (if k < 4 * i then G[k]! * 8347681 else G[k]!).val

/-- `8347681 · 2³² mod q` in the doublewords of `xmm13` and `xmm12`. -/
theorem scale_zlanes (x : BitVec 128) (hx : x = shufDwords ((0 : BitVec 64) ++ BitVec.setWidth 64 16382#32) 0) :
    ZLanes x (fun _ => 8347681) ∧ ZOdd x x := by
  subst hx
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide

/-- The body of the loop of `vscale`. -/
abbrev sbody : List Instr :=
  [.movdquLoad .xmm3 (at_ .rdx 0)] ++ vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++
    vcsub .xmm3 .xmm2 ++ [.movdquStore (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 16)] ++
    [.alu .sub .rcx (.imm 1)]

/-- The product of the doublewords of `xmm3` by the constant, reduced. -/
theorem vmul3_ok {s : State} (hc : VConsts s) :
    WP isa (.block (vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++ vcsub .xmm3 .xmm2)) s fun s' =>
      s'.xmm .xmm3 = csubV (montV (s.xmm .xmm3) (s.xmm .xmm13) (s.xmm .xmm12)) ∧
        XOnly [.xmm3, .xmm2, .xmm4] s s' := by
  simp only [vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  exact ⟨rfl, by xonly⟩

theorem vscale_step {fP : Addr} {G : Poly} {i : Nat} (hi : i < 64) {s : State} (hc : VConsts s)
    (hz : ZLanes (s.xmm .xmm13) (fun _ => 8347681)) (ho : ZOdd (s.xmm .xmm13) (s.xmm .xmm12))
    (hdx : s.gpr .rdx = coeffAddr fP (4 * i)) (hS : Scaled s.mem fP G i) (hw : pR fP ∈ s.wr) :
    WP isa (.block sbody) s fun s' =>
      Scaled s'.mem fP G (i + 1) ∧ s'.gpr .rdx = coeffAddr fP (4 * (i + 1)) ∧
        Frame [pR fP] s.mem s'.mem ∧ VConsts s' ∧ s'.xmm .xmm13 = s.xmm .xmm13 ∧
        s'.xmm .xmm12 = s.xmm .xmm12 ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : 4 * i + 4 ≤ 256 := by omega
  have r0 : InRegions (s.rd ++ s.wr) (coeffAddr fP (4 * i)) 16 := f_in (List.mem_append_right _ hw) j0
  have w0 := f_in hw j0
  have hx : DLanes (s.mem.readW (coeffAddr fP (4 * i)) 128) (fun e => G[4 * i + e]!) := fun e he => by
    rw [dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, hS _ (by omega), ifn (by omega)]
  rw [show sbody = [.movdquLoad .xmm3 (at_ .rdx 0)] ++ ((vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++
      vcsub .xmm3 .xmm2) ++ [.movdquStore (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 16), .alu .sub .rcx (.imm 1)])
    from rfl, WP.block_append_iff]
  vrund [hdx, r0]
  rw [WP.block_append_iff]
  refine WP.mono (vmul3_ok (hc.setXmm (by decide) (by decide) _)) fun s2 ⟨h3, o2⟩ => ?_
  have c2 := xonly_vconsts o2 (hc.setXmm (by decide) (by decide) _) (by decide) (by decide)
  have g2 : s2.gpr = s.gpr := o2.gpr
  have m2 : s2.mem = s.mem := o2.mem
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨o2.rd, o2.wr⟩
  have x2 : s2.mxcsr = s.mxcsr := o2.mxcsr
  have z2 : s2.xmm .xmm13 = s.xmm .xmm13 := by rw [o2.xmm _ (by decide), xmm_setXmm]; rfl
  have z2' : s2.xmm .xmm12 = s.xmm .xmm12 := by rw [o2.xmm _ (by decide), xmm_setXmm]; rfl
  rw [xmm_setXmm, ifp rfl, xmm_setXmm, ifn (by decide), xmm_setXmm, ifn (by decide)] at h3
  generalize hV : csubV (montV (s.mem.readW (coeffAddr fP (4 * i)) 128) (s.xmm .xmm13) (s.xmm .xmm12)) = V at h3
  vrund [g2, m2, e2.1, e2.2, hdx, w0, x2, h3]
  refine ⟨fun k hk => ?_, by rw [show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_add,
    Nat.mul_succ], (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pR_contains fP j0), ⟨?_, ?_⟩, ?_, ?_,
    ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [coeffAt_write128 _ _ j0 _ (by omega)]
    split
    · rename_i h
      rw [ifp (by omega), ← hV, dword_csubV _ (by omega), mulZ (hx _ (by omega)) (hz _ (by omega))
        (dword_montV ho (prod_lt hx hz) (by omega))]
      dsimp only
      rw [show 4 * i + (k - 4 * i) = k by omega, Fin.mul_comm]
    · rename_i h
      rw [hS k hk]
      by_cases h' : k < 4 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact c2.q
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact c2.qinv
  · exact z2
  · exact z2'
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

/-- Every coefficient times `8347681`. -/
theorem vscale_ok {fP sP : Addr} (_hd : (pR sP).Disjoint (pR fP)) {G : Poly} (s : State) (hc : VConsts s)
    (hdi : s.gpr .rdi = fP) (_hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP G) (_hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (_hw : pR sP ∈ s.wr) :
    WP isa vscale s fun s' => PolyIs s'.mem fP (G.map (· * 8347681)) ∧ BInv fP s s' := by
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧
      w.xmm .xmm13 = shufDwords ((0 : BitVec 64) ++ BitVec.setWidth 64 16382#32) 0 ∧
      w.xmm .xmm12 = w.xmm .xmm13 ∧ VConsts w ∧ Keep [.rdx, .rax] s w ∧ w.mem = s.mem ∧ w.mxcsr = s.mxcsr)
    (by
      vrund [hdi, eval_movdqa]
      refine ⟨⟨?_, ?_⟩, ⟨fun r hr => ?_, rfl, rfl⟩⟩
      · simp only [RegUpd.xmm_setReg, xmm_setXmm, reduceCtorEq, ite_false]; exact hc.q
      · simp only [RegUpd.xmm_setReg, xmm_setXmm, reduceCtorEq, ite_false]; exact hc.qinv
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr.1, hr.2, ite_false]) fun w ⟨hdx, h13, h12, hcw, kw, mw, xw⟩ => ?_)
  obtain ⟨hz, ho⟩ := scale_zlanes _ h13
  replace ho : ZOdd (w.xmm .xmm13) (w.xmm .xmm12) := by rw [h12]; exact ho
  refine WP.mono (wp_rcxLoop (N := 64) (by decide) (by decide)
    (fun i u => Scaled u.mem fP G i ∧ u.gpr .rdx = coeffAddr fP (4 * i) ∧ VConsts u ∧
      u.xmm .xmm13 = w.xmm .xmm13 ∧ u.xmm .xmm12 = w.xmm .xmm12 ∧ Keep [.rcx, .rdx] w u ∧
      Frame [pR fP] w.mem u.mem ∧ u.mxcsr = w.mxcsr)
    (fun u o _ => ⟨fun k hk => by rw [o.mem, mw, ifn (by omega)]; exact polyIs_toNat hS (by rw [n_eq]; exact hk),
      by rw [o.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      gonly_vconsts o hcw, by rw [o.xmm], by rw [o.xmm], o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _,
      o.mxcsr⟩)
    (fun i hi u ⟨hS', hdx', hc', hz', hzo', hk', hf', hx'⟩ => WP.mono (vscale_step hi hc' (by rw [hz']; exact hz)
        (by rw [hz', hzo']; exact ho) hdx' hS' (by rw [hk'.2.2, kw.2.2]; exact hwf))
      fun u' ⟨hS'', hdx'', hf'', hc'', hz'', hzo'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', by rw [hz'', hz'], by rw [hzo'', hzo'], (hk'.trans hk'').mono (by simp),
          hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩)) fun u ⟨hS', _, hc', _, _, hk', hf', hx'⟩ => ?_
  refine ⟨polyIs_of_toNat fun k hk => ?_, ⟨(kw.trans hk').mono (by simp), by rw [← mw]; exact hf', hc',
    by rw [hx', xw]⟩⟩
  rw [n_eq] at hk
  rw [hS' k hk, ifp (by omega), map_mul_get _ _ (by rw [n_eq]; exact hk)]

theorem nttInv_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.nttInv s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine mx_correct s hs (by decide +kernel) (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    WP.mono (nttBody_ok hs k1 f1
      (G := (nttInvLens.foldl nttInvLayer (polyAt s.mem (s.gpr .rdi))).map (· * 8347681))
      fun s2 hI hdi hsi hwf hw => ?_) fun s' ⟨hP, hf⟩ => ⟨by rw [nttInv_eq_layers]; exact hP, hf⟩
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
  refine LI.seq hdi hsi hwf hw hd (invLay1_ok hd) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (invLay2_ok hd) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (invLay_ok hd 4 63 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (invLay_ok hd 8 31 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (invLay_ok hd 16 15 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (invLay_ok hd 32 7 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (invLay_ok hd 64 3 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (invLay_ok hd 128 1 (by decide) (by decide)) ?_ hI
  exact fun _ hI => LI.last hdi hsi hwf hw hd (vscale_ok hd) hI

theorem nttInv_ct : ConstantTime isa (inPlaceK nttInv).pre (inPlaceK nttInv).pub Impl.MlDsa.X86_64.Arith.nttInv :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

theorem nttInv_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.nttInv (Spec.MlDsa.nttInvContract X86_64.abi) :=
  Verified.of_correct nttInv_correct nttInv_ct (by
    mldsa_implies [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith
