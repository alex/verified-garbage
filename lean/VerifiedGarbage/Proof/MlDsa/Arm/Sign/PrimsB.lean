import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Prims

/-!
# ML-DSA signing on ARMv7: calls of the NTTs, products and two samplers

Untrusted: everything here is checked by Lean. As `Prims.lean`, for
`vg_mldsa_ntt`, `vg_mldsa_inv_ntt`, `vg_mldsa_multiply_ntt`,
`vg_mldsa_multiply_add_ntt`, `vg_mldsa_rej_ntt_poly` and
`vg_mldsa_expand_mask_poly`. `RejNTTPoly`'s result is public in two runs
whose seeds agree (`rejCall_tr`), and it succeeds only if the algorithm
finishes within `maxBounds` (`rejCall_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (setWidth_append32)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## `NTT` and `NTT⁻¹` in place -/

/-- What a call of an in-place transformation of `f` needs of the layout. -/
def ipChk (bs wbs : List (Reg × Nat)) (f : Ptr) : Bool :=
  inB wbs f 1024 && inB wbs (sc oPS) 1024 && inB bs f 1024 && inB bs (sc oPS) 1024 &&
    sepB bs f 1024 (sc oPS) 1024 && decide (f.1 ∈ bases)

theorem ipChk_spec {bs wbs : List (Reg × Nat)} {f : Ptr} (h : ipChk bs wbs f = true) :
    inB wbs f 1024 = true ∧ inB wbs (sc oPS) 1024 = true ∧ inB bs f 1024 = true ∧ inB bs (sc oPS) 1024 = true ∧
      sepB bs f 1024 (sc oPS) 1024 = true ∧ ([Arg.ptr f, .ptr (sc oPS)].all Arg.ok) = true := by
  simp only [ipChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, by simp [Arg.ok, h.2]⟩

theorem ipPre {t : Poly → Poly} {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {f : Ptr}
    (hc : ipChk (rbs ++ wbs) wbs f = true) (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2)
    (g1 : E.gpr .r1 = s.gpr .r7 + BitVec.ofNat 32 oPS) (hrd : E.rd = [])
    (hwr : E.wr = [pR (pa s f), pR (pa s (sc oPS))]) (hr : Reduced s.mem (pa s f)) :
    (inPlaceContract Arm.abi t S).pre E := by
  obtain ⟨_, _, i1, i2, d12, _⟩ := ipChk_spec hc
  sig_pre [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, En.L.w i1 (by decide), En.L.w (p := sc oPS) i2 (by decide)]
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.conj (bs := [(f, 1024), (sc oPS, 1024)]) (by simp [i1, i2]),
    En.L.fit i1 (by decide), En.L.fit (p := sc oPS) i2 (by decide), En.red i1 hr⟩

theorem ipAt_ok {t : Poly → Poly} {n : String} {c : Prog isa}
    (C : Callee (fun S => inPlaceContract Arm.abi t S) 0 D c) {s : State} (L : Lay D rbs wbs s) {f : Ptr}
    (hc : ipChk (rbs ++ wbs) wbs f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (callR n c [.ptr f, .ptr (sc oPS)]) s fun s' => PPostB D s s' [(f, 1024), (sc oPS, 1024)] ∧
      CS s s' ∧ PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f))) := by
  obtain ⟨w1, w2, i1, _, _, ok⟩ := ipChk_spec hc
  refine WP.mono (callR_ok C.ver.1 (by have := C.su; have := C.hS; omega) ok L.sp
    (rd := []) (wr := [pR (pa s f), pR (pa s (sc oPS))])
    (fun s1 hA k => ipPre (ent_R L k (by have := C.hS; omega) _ _) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn2 hA).2) rfl rfl hr)
    (covers_append covers_nil (covers_wr (covers_cons (L.cW w1) (L.cW w2)))) (covers_cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, _⟩ := argsIn2 hA
  sig_post [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, Arg.val, k.mem, L.w i1 (by decide)] at hq
  exact hq

theorem ipAt_tr {t : Poly → Poly} {n : String} {c : Prog isa}
    (C : Callee (fun S => inPlaceContract Arm.abi t S) 0 D c) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f))
      (callR n c [.ptr f, .ptr (sc oPS)]) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, _, ok⟩ := ipChk_spec hc
  have hS : C.S ≤ D := by have := C.hS; omega
  refine callR_tr C.ver.1 C.ver.2.1 ok fun x y x1 y1 ⟨R, rx, ry⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, ipPre (ent_R R.lx kx hS [] [pR (pa x f), pR (pa x (sc oPS))]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn2 hAx).2) rfl rfl rx,
      ipPre (ent_R R.ly ky hS [] [pR (pa y f), pR (pa y (sc oPS))]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn2 hAy).2) rfl rfl ry, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append covers_nil (covers_wr (covers_cons (R.lx.cW w1) (R.lx.cW w2))),
      by rw [kx.wr]; exact covers_cons (R.lx.cW w1) (R.lx.cW w2),
      by rw [ky.rd, ky.wr]; exact covers_append covers_nil (covers_wr (covers_cons (R.ly.cW w1) (R.ly.cW w2))),
      by rw [ky.wr]; exact covers_cons (R.ly.cW w1) (R.ly.cW w2)⟩
  obtain ⟨hx1, hx2⟩ := argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := argsIn2 hAy
  sig_pub [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hy1, hy2, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

theorem nttAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f : Ptr}
    (hc : ipChk (rbs ++ wbs) wbs f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (nttAt P f) s fun s' => PPostB D s s' [(f, 1024), (sc oPS, 1024)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s f) (ntt (polyAt s.mem (pa s f))) :=
  ipAt_ok hP.ntt L hc hr

theorem invNttAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f : Ptr}
    (hc : ipChk (rbs ++ wbs) wbs f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (invNttAt P f) s fun s' => PPostB D s s' [(f, 1024), (sc oPS, 1024)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s f) (nttInv (polyAt s.mem (pa s f))) :=
  ipAt_ok hP.invNtt L hc hr

theorem nttAt_tr {P : Prims} (hP : PrimsOk P D) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f))
      (nttAt P f) fun _ _ => True :=
  ipAt_tr hP.ntt hc

theorem invNttAt_tr {P : Prims} (hP : PrimsOk P D) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f))
      (invNttAt P f) fun _ _ => True :=
  ipAt_tr hP.invNtt hc

/-! ## Products -/

/-- What a call of `vg_mldsa_multiply_ntt` or `vg_mldsa_multiply_add_ntt` on
`h`, `f`, `g` needs of the layout. -/
def mulChk (bs wbs : List (Reg × Nat)) (h f g : Ptr) : Bool :=
  inB wbs h 1024 && inB bs h 1024 && inB bs f 1024 && inB bs g 1024 && sepB bs h 1024 f 1024 &&
    sepB bs h 1024 g 1024 && decide (h.1 ∈ bases) && decide (f.1 ∈ bases) && decide (g.1 ∈ bases)

theorem mulChk_spec {bs wbs : List (Reg × Nat)} {h f g : Ptr} (hc : mulChk bs wbs h f g = true) :
    inB wbs h 1024 = true ∧ inB bs h 1024 = true ∧ inB bs f 1024 = true ∧ inB bs g 1024 = true ∧
      sepB bs h 1024 f 1024 = true ∧ sepB bs h 1024 g 1024 = true ∧
      ([Arg.ptr h, .ptr f, .ptr g].all Arg.ok) = true := by
  simp only [mulChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, by simp [Arg.ok, h7, h8, h9]⟩

theorem mulPre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {h f g : Ptr}
    (hc : mulChk (rbs ++ wbs) wbs h f g = true) (g0 : E.gpr .r0 = s.gpr h.1 + BitVec.ofNat 32 h.2)
    (g1 : E.gpr .r1 = s.gpr f.1 + BitVec.ofNat 32 f.2) (g2 : E.gpr .r2 = s.gpr g.1 + BitVec.ofNat 32 g.2)
    (hrd : E.rd = [pR (pa s f), pR (pa s g)]) (hwr : E.wr = [pR (pa s h)])
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    (mulContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, i3, d12, d13, _⟩ := mulChk_spec hc
  sig_pre [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, En.L.w i1 (by decide), En.L.w i2 (by decide), En.L.w i3 (by decide)]
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13,
    En.conj (bs := [(h, 1024), (f, 1024), (g, 1024)]) (by simp [i1, i2, i3]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), En.L.fit i3 (by decide), En.red i2 rf, En.red i3 rg⟩

theorem mulAddPre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {h f g : Ptr}
    (hc : mulChk (rbs ++ wbs) wbs h f g = true) (g0 : E.gpr .r0 = s.gpr h.1 + BitVec.ofNat 32 h.2)
    (g1 : E.gpr .r1 = s.gpr f.1 + BitVec.ofNat 32 f.2) (g2 : E.gpr .r2 = s.gpr g.1 + BitVec.ofNat 32 g.2)
    (hrd : E.rd = [pR (pa s f), pR (pa s g)]) (hwr : E.wr = [pR (pa s h)])
    (rh : Reduced s.mem (pa s h)) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    (mulAddContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, i3, d12, d13, _⟩ := mulChk_spec hc
  sig_pre [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, En.L.w i1 (by decide), En.L.w i2 (by decide), En.L.w i3 (by decide)]
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13,
    En.conj (bs := [(h, 1024), (f, 1024), (g, 1024)]) (by simp [i1, i2, i3]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), En.L.fit i3 (by decide), En.red i1 rh, En.red i2 rf,
    En.red i3 rg⟩

theorem mulAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {h f g : Ptr}
    (hc : mulChk (rbs ++ wbs) wbs h f g = true) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (mulAt P h f g) s fun s' => PPostB D s s' [(h, 1024)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s h) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := mulChk_spec hc
  refine WP.mono (callR_ok hP.mul.ver.1 (by have := hP.mul.su; have := hP.mul.hS; omega) ok L.sp
    (rd := [pR (pa s f), pR (pa s g)]) (wr := [pR (pa s h)])
    (fun s1 hA k => mulPre (ent_R L k (by have := hP.mul.hS; omega) _ _) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hA).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hA).2.2) rfl rfl rf rg)
    (covers_append (covers_cons (L.cR i2) (L.cR i3)) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  sig_post [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, Arg.val, k.mem, L.w i1 (by decide), L.w i2 (by decide), L.w i3 (by decide)] at hq
  exact hq

theorem mulAddAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {h f g : Ptr}
    (hc : mulChk (rbs ++ wbs) wbs h f g = true) (rh : Reduced s.mem (pa s h)) (rf : Reduced s.mem (pa s f))
    (rg : Reduced s.mem (pa s g)) :
    WP isa (mulAddAt P h f g) s fun s' => PPostB D s s' [(h, 1024)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s h)
        (add (polyAt s.mem (pa s h)) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g)))) := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := mulChk_spec hc
  refine WP.mono (callR_ok hP.mulAdd.ver.1 (by have := hP.mulAdd.su; have := hP.mulAdd.hS; omega) ok L.sp
    (rd := [pR (pa s f), pR (pa s g)]) (wr := [pR (pa s h)])
    (fun s1 hA k => mulAddPre (ent_R L k (by have := hP.mulAdd.hS; omega) _ _) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hA).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hA).2.2) rfl rfl rh rf rg)
    (covers_append (covers_cons (L.cR i2) (L.cR i3)) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  sig_post [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, Arg.val, k.mem, L.w i1 (by decide), L.w i2 (by decide), L.w i3 (by decide)] at hq
  exact hq

theorem mulAt_tr {P : Prims} (hP : PrimsOk P D) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (mulAt P h f g) fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := mulChk_spec hc
  have hS : hP.mul.S ≤ D := by have := hP.mul.hS; omega
  refine callR_tr hP.mul.ver.1 hP.mul.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rfx, rgx⟩, ⟨rfy, rgy⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, mulPre (ent_R R.lx kx hS [pR (pa x f), pR (pa x g)] [pR (pa x h)]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAx).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAx).2.2) rfl rfl rfx rgx,
      mulPre (ent_R R.ly ky hS [pR (pa y f), pR (pa y g)] [pR (pa y h)]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAy).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAy).2.2) rfl rfl rfy rgy, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append (covers_cons (R.lx.cR i2) (R.lx.cR i3)) (covers_wr (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact covers_append (covers_cons (R.ly.cR i2) (R.ly.cR i3)) (covers_wr (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  sig_pub [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.eq i1, R.eq i2, R.eq i3, R.sp, and_self]

theorem mulAddAt_tr {P : Prims} (hP : PrimsOk P D) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧
      (Reduced x.mem (pa x h) ∧ Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y h) ∧ Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (mulAddAt P h f g)
      fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := mulChk_spec hc
  have hS : hP.mulAdd.S ≤ D := by have := hP.mulAdd.hS; omega
  refine callR_tr hP.mulAdd.ver.1 hP.mulAdd.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rhx, rfx, rgx⟩, ⟨rhy, rfy, rgy⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, mulAddPre (ent_R R.lx kx hS [pR (pa x f), pR (pa x g)] [pR (pa x h)]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAx).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAx).2.2) rfl rfl rhx rfx rgx,
      mulAddPre (ent_R R.ly ky hS [pR (pa y f), pR (pa y g)] [pR (pa y h)]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAy).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAy).2.2) rfl rfl rhy rfy rgy, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append (covers_cons (R.lx.cR i2) (R.lx.cR i3)) (covers_wr (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact covers_append (covers_cons (R.ly.cR i2) (R.ly.cR i3)) (covers_wr (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  sig_pub [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.eq i1, R.eq i2, R.eq i3, R.sp, and_self]

end

end VG.Proof.MlDsa.Arm.Sign
