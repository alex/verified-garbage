import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Prims

/-!
# ML-DSA signing on ARMv7: calls of the samplers

As `Prims.lean`, for `vg_mldsa_rej_ntt_poly`, `vg_mldsa_expand_mask_poly` and
`vg_mldsa_sample_in_ball` (whose fifth argument is on the stack). The results
of `RejNTTPoly` and `SampleInBall` are public in two runs whose seeds agree
(`rejCall_tr`, `ballCall_tr`), and they succeed only if the algorithm finishes
within `maxBounds` (`rejCall_ok`, `ballCall_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (setWidth_append32 push2_arg)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## `RejNTTPoly` -/

/-- What a call of `vg_mldsa_rej_ntt_poly` to `a` needs of the layout. -/
def rejChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  inB wbs a 1024 && inB wbs (sc oPS) 2048 && inB bs (sc oRS) 34 && inB bs a 1024 && inB bs (sc oPS) 2048 &&
    sepB bs (sc oRS) 34 a 1024 && sepB bs (sc oRS) 34 (sc oPS) 2048 && sepB bs a 1024 (sc oPS) 2048 &&
    decide (a.1 ∈ bases)

theorem rejChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : rejChk bs wbs a = true) :
    inB wbs a 1024 = true ∧ inB wbs (sc oPS) 2048 = true ∧ inB bs (sc oRS) 34 = true ∧ inB bs a 1024 = true ∧
      inB bs (sc oPS) 2048 = true ∧ sepB bs (sc oRS) 34 a 1024 = true ∧ sepB bs (sc oRS) 34 (sc oPS) 2048 = true ∧
      sepB bs a 1024 (sc oPS) 2048 = true ∧ ([Arg.ptr (sc oRS), .ptr a, .ptr (sc oPS)].all Arg.ok) = true := by
  simp only [rejChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by simp [Arg.ok, h9]⟩

theorem rejPre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {a : Ptr}
    (hc : rejChk (rbs ++ wbs) wbs a = true) (g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oRS)
    (g1 : E.gpr .r1 = s.gpr a.1 + BitVec.ofNat 32 a.2) (g2 : E.gpr .r2 = s.gpr .r7 + BitVec.ofNat 32 oPS)
    (hrd : E.rd = [⟨pa s (sc oRS), 34⟩]) (hwr : E.wr = [pR (pa s a), ⟨pa s (sc oPS), 2048⟩]) :
    (rejNTTContract Arm.abi S).pre E := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := rejChk_spec hc
  sig_pre [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, En.L.w (p := sc oRS) i1 (by decide), En.L.w i2 (by decide),
    En.L.w (p := sc oPS) i3 (by decide)]
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13, En.L.disj d23,
    En.conj (bs := [(sc oRS, 34), (a, 1024), (sc oPS, 2048)]) (by simp [i1, i2, i3]),
    En.L.fit (p := sc oRS) i1 (by decide), En.L.fit i2 (by decide), En.L.fit (p := sc oPS) i3 (by decide)⟩

/-- The call of `vg_mldsa_rej_ntt_poly`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds`. -/
theorem rejCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {a : Ptr}
    (hc : rejChk (rbs ++ wbs) wbs a = true) :
    WP isa (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)]) s fun s' =>
      PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ CS s s' ∧
      (s'.gpr .r0 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)) (s'.gpr .r0)
        (polyAt s'.mem (pa s a)) ∧
      (s'.gpr .r0 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := rejChk_spec hc
  refine WP.mono (callR_ok (hv_with hP.rejNTT.ver.1 hP.rejMax) (by have := hP.rejNTT.su; have := hP.rejNTT.hS; omega)
    ok L.sp (rd := [⟨pa s (sc oRS), 34⟩]) (wr := [pR (pa s a), ⟨pa s (sc oPS), 2048⟩])
    (fun s1 hA k => rejPre (ent_R L k (by have := hP.rejNTT.hS; omega) _ _) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hA).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hA).2.2) rfl rfl)
    (covers_append (L.cR i1) (covers_wr (covers_cons (L.cW w1) (L.cW w2)))) (covers_cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  sig_post [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, Arg.val, k.mem, setWidth_append32,
    L.w (p := sc oRS) i1 (by decide), L.w i2 (by decide)] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, vR _ _ _ nl0, State.callEntry_mem, e1, Arg.val, k.mem,
    State.addr, L.w (p := sc oRS) i1 (by decide)] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem rejCall_tr {P : Prims} (hP : PrimsOk P D) {a : Ptr} (hc : rejChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34)
      (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)])
      fun x y => x.gpr .r0 = y.gpr .r0 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := rejChk_spec hc
  have hS : hP.rejNTT.S ≤ D := by have := hP.rejNTT.hS; omega
  refine callRRet_tr hP.rejNTT.ver.1 hP.rejRet ok
    fun x y x1 y1 ⟨R, hb⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, rejPre (ent_R R.lx kx hS [⟨pa x (sc oRS), 34⟩] [pR (pa x a), ⟨pa x (sc oPS), 2048⟩]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAx).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAx).2.2) rfl rfl,
      rejPre (ent_R R.ly ky hS [⟨pa y (sc oRS), 34⟩] [pR (pa y a), ⟨pa y (sc oPS), 2048⟩]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAy).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAy).2.2) rfl rfl, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append (R.lx.cR i1) (covers_wr (covers_cons (R.lx.cW w1) (R.lx.cW w2))),
      by rw [kx.wr]; exact covers_cons (R.lx.cW w1) (R.lx.cW w2),
      by rw [ky.rd, ky.wr]; exact covers_append (R.ly.cR i1) (covers_wr (covers_cons (R.ly.cW w1) (R.ly.cW w2))),
      by rw [ky.wr]; exact covers_cons (R.ly.cW w1) (R.ly.cW w2)⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  sig_pub [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, kx.mem, ky.mem, hx1, hx2, hx3, hy1, hy2, hy3, Arg.val,
    R.lx.w (p := sc oRS) i1 (by decide), R.ly.w (p := sc oRS) i1 (by decide), hb]
  simp only [R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `ExpandMask` -/

/-- What a call of `vg_mldsa_expand_mask_poly` to `a` needs of the layout. -/
def maskChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  inB wbs a 1024 && inB wbs (sc oPS) 2048 && inB bs (sc oMS) 66 && inB bs a 1024 && inB bs (sc oPS) 2048 &&
    sepB bs (sc oMS) 66 a 1024 && sepB bs (sc oMS) 66 (sc oPS) 2048 && sepB bs a 1024 (sc oPS) 2048 &&
    decide (a.1 ∈ bases)

theorem maskChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : maskChk bs wbs a = true) :
    inB wbs a 1024 = true ∧ inB wbs (sc oPS) 2048 = true ∧ inB bs (sc oMS) 66 = true ∧ inB bs a 1024 = true ∧
      inB bs (sc oPS) 2048 = true ∧ sepB bs (sc oMS) 66 a 1024 = true ∧ sepB bs (sc oMS) 66 (sc oPS) 2048 = true ∧
      sepB bs a 1024 (sc oPS) 2048 = true ∧ a.1 ∈ bases := by
  simp only [maskChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem maskPre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : maskChk (rbs ++ wbs) wbs a = true)
    (g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oMS) (g1 : E.gpr .r1 = BitVec.ofNat 32 γ)
    (g2 : E.gpr .r2 = s.gpr a.1 + BitVec.ofNat 32 a.2) (g3 : E.gpr .r3 = s.gpr .r7 + BitVec.ofNat 32 oPS)
    (hrd : E.rd = [⟨pa s (sc oMS), 66⟩]) (hwr : E.wr = [pR (pa s a), ⟨pa s (sc oPS), 2048⟩]) :
    (expandMaskContract Arm.abi S).pre E := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := maskChk_spec hc
  have hγ' : γ < 2 ^ 32 := by omega
  sig_pre [expandMaskContract, expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.L.w (p := sc oMS) i1 (by decide), En.L.w i2 (by decide),
    En.L.w (p := sc oPS) i3 (by decide), toNat32 hγ']
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13, En.L.disj d23,
    En.conj (bs := [(sc oMS, 66), (a, 1024), (sc oPS, 2048)]) (by simp [i1, i2, i3]),
    En.L.fit (p := sc oMS) i1 (by decide), En.L.fit i2 (by decide), En.L.fit (p := sc oPS) i3 (by decide), hγ⟩

theorem maskArgs_ok {a : Ptr} {γ : Nat} (b1 : a.1 ∈ bases) :
    [Arg.ptr (sc oMS), .imm γ, .ptr a, .ptr (sc oPS)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem maskAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : maskChk (rbs ++ wbs) wbs a = true) :
    WP isa (maskAt P γ a) s fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s (sc oMS)) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := maskChk_spec hc
  have hγ' : γ < 2 ^ 32 := by omega
  refine WP.mono (callR_ok hP.expandMask.ver.1 (by have := hP.expandMask.su; have := hP.expandMask.hS; omega)
    (maskArgs_ok b1) L.sp (rd := [⟨pa s (sc oMS), 66⟩]) (wr := [pR (pa s a), ⟨pa s (sc oPS), 2048⟩])
    (fun s1 hA k => maskPre (ent_R L k (by have := hP.expandMask.hS; omega) _ _) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hA).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hA).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hA).2.2.2) rfl rfl)
    (covers_append (L.cR i1) (covers_wr (covers_cons (L.cW w1) (L.cW w2)))) (covers_cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3, _⟩ := argsIn4 hA
  sig_post [expandMaskContract, expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, Arg.val, k.mem, toNat32 hγ', L.w (p := sc oMS) i1 (by decide), L.w i2 (by decide)] at hq
  exact hq

theorem maskAt_tr {P : Prims} (hP : PrimsOk P D) {γ : Nat} {a : Ptr} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19)
    (hc : maskChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (LRel D rbs wbs) (maskAt P γ a) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := maskChk_spec hc
  have hS : hP.expandMask.S ≤ D := by have := hP.expandMask.hS; omega
  refine callR_tr hP.expandMask.ver.1 hP.expandMask.ver.2.1 (maskArgs_ok b1)
    fun x y x1 y1 R ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, maskPre (ent_R R.lx kx hS [⟨pa x (sc oMS), 66⟩] [pR (pa x a), ⟨pa x (sc oPS), 2048⟩]) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hAx).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hAx).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hAx).2.2.2) rfl rfl,
      maskPre (ent_R R.ly ky hS [⟨pa y (sc oMS), 66⟩] [pR (pa y a), ⟨pa y (sc oPS), 2048⟩]) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hAy).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hAy).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hAy).2.2.2) rfl rfl, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append (R.lx.cR i1) (covers_wr (covers_cons (R.lx.cW w1) (R.lx.cW w2))),
      by rw [kx.wr]; exact covers_cons (R.lx.cW w1) (R.lx.cW w2),
      by rw [ky.rd, ky.wr]; exact covers_append (R.ly.cR i1) (covers_wr (covers_cons (R.ly.cW w1) (R.ly.cW w2))),
      by rw [ky.wr]; exact covers_cons (R.ly.cW w1) (R.ly.cW w2)⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := argsIn4 hAy
  sig_pub [expandMaskContract, expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `SampleInBall` -/

/-- What a call of `vg_mldsa_sample_in_ball` of the `len` bytes at `CT` to `c` needs of the layout. -/
def ballChk (bs wbs : List (Reg × Nat)) (len : Nat) (c : Ptr) : Bool :=
  inB wbs c 1024 && inB wbs (sc oPS) 2048 && inB bs (sc oCT) len && inB bs c 1024 && inB bs (sc oPS) 2048 &&
    sepB bs (sc oCT) len c 1024 && sepB bs (sc oCT) len (sc oPS) 2048 && sepB bs c 1024 (sc oPS) 2048 &&
    decide (c.1 ∈ bases)

theorem ballChk_spec {bs wbs : List (Reg × Nat)} {len : Nat} {c : Ptr} (hc : ballChk bs wbs len c = true) :
    inB wbs c 1024 = true ∧ inB wbs (sc oPS) 2048 = true ∧ inB bs (sc oCT) len = true ∧ inB bs c 1024 = true ∧
      inB bs (sc oPS) 2048 = true ∧ sepB bs (sc oCT) len c 1024 = true ∧ sepB bs (sc oCT) len (sc oPS) 2048 = true ∧
      sepB bs c 1024 (sc oPS) 2048 = true ∧ c.1 ∈ bases := by
  simp only [ballChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem ballArgs_ok {len tau : Nat} {c : Ptr} (b1 : c.1 ∈ bases) :
    [Arg.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem ballParams_lt {len tau : Nat} (hp : (len, tau) ∈ ballParams) : 0 < len ∧ len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
  simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega

theorem ballPre {S : Nat} (hS : S + 8 ≤ D) {s E : State} (En : Ent D rbs wbs s S E) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : ballChk (rbs ++ wbs) wbs len c = true)
    (hsp : E.sp = s.sp - BitVec.ofNat 32 8) (ha : stackArgAddr E 0 = State.addr s.sp - BitVec.ofNat 64 8)
    (hv : stackArg E 0 = s.gpr .r7 + BitVec.ofNat 32 oPS)
    (g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oCT) (g1 : E.gpr .r1 = BitVec.ofNat 32 len)
    (g2 : E.gpr .r2 = BitVec.ofNat 32 tau) (g3 : E.gpr .r3 = s.gpr c.1 + BitVec.ofNat 32 c.2)
    (hrd : E.rd = [⟨pa s (sc oCT), len⟩, argR s]) (hwr : E.wr = [pR (pa s c), ⟨pa s (sc oPS), 2048⟩]) :
    (sampleInBallContract Arm.abi S).pre E := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := ballChk_spec hc
  obtain ⟨l0, l1, l2⟩ := ballParams_lt hp
  have h8 : 8 ≤ s.sp.toNat := by have := En.L.sp; omega
  have e8 : E.sp.toNat = s.sp.toNat - 8 := by rw [hsp, sp_sub8 h8]
  sig_pre [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, ha, hv, En.L.w (p := sc oCT) i1 (by omega), En.L.w i2 (by decide),
    En.L.w (p := sc oPS) i3 (by decide), toNat32 l1, toNat32 l2]
  have hD : 8 ≤ D := by omega
  refine ⟨wf4 En.wf (by have := s.sp.isLt; omega), hrd, hwr, En.L.disj d12, En.L.disj d13, En.L.disj d23,
    (argR_disj En.L hD i2).symm, (argR_disj (p := sc oPS) En.L hD i3).symm,
    conj_stk [⟨pa s (sc oCT), len⟩, pR (pa s c), ⟨pa s (sc oPS), 2048⟩, argR s] ?_,
    En.L.fit (p := sc oCT) i1 (by omega), En.L.fit i2 (by decide), En.L.fit (p := sc oPS) i3 (by decide), hp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨En.stk _ _ i1, En.stk _ _ i2, En.stk _ _ i3, hsp ▸ argR_stk En.L hS⟩

/-- The regions `SampleInBall` is given. -/
abbrev ballRd (s : State) (len : Nat) : List Region := [⟨pa s (sc oCT), len⟩]
abbrev ballWr (s : State) (c : Ptr) : List Region := [pR (pa s c), ⟨pa s (sc oPS), 2048⟩]

theorem ballPre' {P : Prims} (hP : PrimsOk P D) {s s1 : State} (L : Lay D rbs wbs s) (k : Keep argRegs s s1)
    {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams) (hc : ballChk (rbs ++ wbs) wbs len c = true)
    (hA : ArgsIn [.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)] s s1) :
    (sampleInBallContract Arm.abi hP.ball.S).pre
      ((pushed [.r12, .lr] s1).callEntry.withRegions (ballRd s len ++ [argR s]) (ballWr s c)) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
  have hS := hP.ball.hS
  obtain ⟨ha, hv⟩ := stk_arg L k (by omega) (ballRd s len ++ [argR s]) (ballWr s c)
  exact ballPre hS (ent_S L k hS _ _) hp hc (by rw [State.withRegions_sp, State.callEntry_sp, pushed_sp8, k.sp]) ha
    (by rw [hv, e4]; rfl) (by rw [vS _ _ _ nl0, e0]; rfl) (by rw [vS _ _ _ nl1, e1]; rfl)
    (by rw [vS _ _ _ nl2, e2]; rfl) (by rw [vS _ _ _ nl3, e3]; rfl) rfl rfl

/-- The call of `vg_mldsa_sample_in_ball`: its outcome, and that it succeeds
only if `SampleInBall` finishes within `maxBounds`. -/
theorem ballCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : ballChk (rbs ++ wbs) wbs len c = true) :
    WP isa (ballAt P len tau c) s fun s' =>
      PPostB D s s' [(c, 1024), (sc oPS, 2048)] ∧ CS s s' ∧
      (s'.gpr .r0 = 1 → Reduced s'.mem (pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (pa s (sc oCT)) len)).map toRq)
        (s'.gpr .r0) (polyAt s'.mem (pa s c)) ∧
      (s'.gpr .r0 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (pa s (sc oCT)) len)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := ballChk_spec hc
  obtain ⟨l0, l1, l2⟩ := ballParams_lt hp
  refine WP.mono (callS_ok (hv_with hP.ball.ver.1 hP.ballMax) (by have := hP.ball.su; have := hP.ball.hS; omega)
    (ballArgs_ok b1) L.sp (rd := ballRd s len) (wr := ballWr s c)
    (fun s1 hA k => ballPre' hP L k hp hc hA) (L.cR i1) (covers_cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, s₂, hm₂, hg₂, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e0, e1, e2, e3, _⟩ := argsIn5 hA
  have En := ent_S (S := hP.ball.S) L k hP.ball.hS (ballRd s len ++ [argR s]) (ballWr s c)
  have er : s₂.gpr .r0 = s'.gpr .r0 := hg₂ .r0 (by decide)
  set E := (pushed [.r12, .lr] s1).callEntry.withRegions (ballRd s len ++ [argR s]) (ballWr s c) with hE
  have g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oCT := by rw [hE, vS _ _ _ nl0, e0]; rfl
  have g1 : E.gpr .r1 = BitVec.ofNat 32 len := by rw [hE, vS _ _ _ nl1, e1]; rfl
  have g2 : E.gpr .r2 = BitVec.ofNat 32 tau := by rw [hE, vS _ _ _ nl2, e2]; rfl
  have g3 : E.gpr .r3 = s.gpr c.1 + BitVec.ofNat 32 c.2 := by rw [hE, vS _ _ _ nl3, e3]; rfl
  have eb := En.bytes (p := sc oCT) i1
  clear_value E
  sig_post [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [g0, g1, g2, g3, hm₂, er, setWidth_append32, toNat32 l1, toNat32 l2,
    L.w (p := sc oCT) i1 (by omega), L.w i2 (by decide), eb] at hq
  simp only [State.withRegions_gpr, g0, g1, g2, er, toNat32 l1, toNat32 l2, State.addr,
    L.w (p := sc oCT) i1 (by omega), eb] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem ballCall_tr {P : Prims} (hP : PrimsOk P D) {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams)
    (hc : ballChk (rbs ++ wbs) wbs len c = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oCT)) len = bytesAt y.mem (pa y (sc oCT)) len)
      (ballAt P len tau c) fun x y => x.gpr .r0 = y.gpr .r0 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := ballChk_spec hc
  obtain ⟨l0, l1, l2⟩ := ballParams_lt hp
  have hS := hP.ball.hS
  refine callSRet_tr hP.ball.ver.1 hP.ballRet (ballArgs_ok b1) (fun x y h => h.1.sp)
    fun x y x1 y1 ⟨R, hb⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, ballPre' hP R.lx kx hp hc hAx, ballPre' hP R.ly ky hp hc hAy, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := argsIn5 hAx
    obtain ⟨hy0, hy1, hy2, hy3, hy4⟩ := argsIn5 hAy
    have Ex := ent_S (S := hP.ball.S) R.lx kx hS (ballRd x len ++ [argR x]) (ballWr x c)
    have Ey := ent_S (S := hP.ball.S) R.ly ky hS (ballRd y len ++ [argR y]) (ballWr y c)
    obtain ⟨-, vx⟩ := stk_arg R.lx kx (by omega) (ballRd x len ++ [argR x]) (ballWr x c)
    obtain ⟨-, vy⟩ := stk_arg R.ly ky (by omega) (ballRd y len ++ [argR y]) (ballWr y c)
    set X := (pushed [.r12, .lr] x1).callEntry.withRegions (ballRd x len ++ [argR x]) (ballWr x c) with hX
    set Y := (pushed [.r12, .lr] y1).callEntry.withRegions (ballRd y len ++ [argR y]) (ballWr y c) with hY
    have gx : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], X.gpr r = x1.gpr r := by
      intro r hr; rw [hX, vS _ _ _ (by revert hr; decide +revert)]
    have gy : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], Y.gpr r = y1.gpr r := by
      intro r hr; rw [hY, vS _ _ _ (by revert hr; decide +revert)]
    have sx : X.sp = x.sp - BitVec.ofNat 32 8 := by rw [hX, State.withRegions_sp, State.callEntry_sp, pushed_sp8, kx.sp]
    have sy : Y.sp = y.sp - BitVec.ofNat 32 8 := by rw [hY, State.withRegions_sp, State.callEntry_sp, pushed_sp8, ky.sp]
    have bx := Ex.bytes (p := sc oCT) i1
    have bY := Ey.bytes (p := sc oCT) i1
    clear_value X Y
    sig_pub [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [gx .r0 (by decide), gx .r1 (by decide), gx .r2 (by decide), gx .r3 (by decide),
      gy .r0 (by decide), gy .r1 (by decide), gy .r2 (by decide), gy .r3 (by decide), sx, sy,
      hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, vx, vy, hx4, hy4, Arg.val, toNat32 l1]
    rw [R.lx.w (p := sc oCT) i1 (by omega), R.ly.w (p := sc oCT) i1 (by omega), bx, bY, hb]
    simp only [R.eq i1, R.eq i2, R.sp, and_self]
  · exact (cov_S R.lx kx (by omega) (R.lx.cR i1) (covers_cons (R.lx.cW w1) (R.lx.cW w2))).1
  · exact (cov_S R.lx kx (by omega) (R.lx.cR i1) (covers_cons (R.lx.cW w1) (R.lx.cW w2))).2
  · exact (cov_S R.ly ky (by omega) (R.ly.cR i1) (covers_cons (R.ly.cW w1) (R.ly.cW w2))).1
  · exact (cov_S R.ly ky (by omega) (R.ly.cR i1) (covers_cons (R.ly.cW w1) (R.ly.cW w2))).2

end

end VG.Proof.MlDsa.Arm.Sign
