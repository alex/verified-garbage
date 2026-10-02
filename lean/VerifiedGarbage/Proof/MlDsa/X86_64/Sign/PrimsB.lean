import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Prims

/-!
# ML-DSA signing on x86-64: calls of addition, subtraction and the samplers

As `Prims.lean`, for `vg_mldsa_add`, `vg_mldsa_sub`, `vg_mldsa_rej_ntt_poly`,
`vg_mldsa_expand_mask_poly` and `vg_mldsa_sample_in_ball`. The samplers'
results are public in two runs whose seeds agree (`rejCall_tr`,
`ballCall_tr`), and they succeed only if the algorithm finishes within
`maxBounds` (`rejCall_ok`, `ballCall_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `k` with the fact `X` of each run added to its postcondition. -/
def withPost (k : Contract isa) (X : State → State → Prop) : Contract isa :=
  { k with post := fun s s' => k.post s s' ∧ X s s' }

theorem hv_with {c : Prog isa} {k : Contract isa} {X : State → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hx : ∀ s t s', k.pre s → Exec isa c s t s' → X s s') :
    ∀ s, (withPost k X).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (withPost k X).post s s' :=
  fun s hs => let ⟨t, s', e, a, p⟩ := hv s hs; ⟨t, s', e, a, p, hx s t s' hs e⟩

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## Addition and subtraction -/

/-- The contract of `vg_mldsa_add` (`t = add`) or `vg_mldsa_sub` (`t = sub`). -/
abbrev accC (t : Poly → Poly → Poly) (S : Nat) : Contract isa :=
  accSig.contract X86_64.abi
    (pre := fun f g m => Reduced m f ∧ Reduced m g)
    (post := fun f g m m' _ => PolyIs m' f (t (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := S)

/-- What a call of `vg_mldsa_add` or `vg_mldsa_sub` on `f`, `g` needs of the layout. -/
def accChk (bs wbs : List (Reg × Nat)) (f g : Ptr) : Bool :=
  inB wbs f 1024 && inB bs f 1024 && inB bs g 1024 && sepB bs f 1024 g 1024 && decide (f.1 ∈ bases) &&
    decide (f.2 < 2 ^ 31) && decide (g.1 ∈ bases) && decide (g.2 < 2 ^ 31)

theorem accChk_spec {bs wbs : List (Reg × Nat)} {f g : Ptr} (hc : accChk bs wbs f g = true) :
    inB wbs f 1024 = true ∧ inB bs f 1024 = true ∧ inB bs g 1024 = true ∧ sepB bs f 1024 g 1024 = true ∧
      ([Arg.ptr f, .ptr g].all Arg.ok) = true := by
  simp only [accChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  exact ⟨h1, h2, h3, h4, by simp [Arg.ok, h5, h6, h7, h8]⟩

theorem accPre {t : Poly → Poly → Poly} {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1)
    {f g : Ptr} (hc : accChk (rbs ++ wbs) wbs f g = true) (hA : ArgsIn [.ptr f, .ptr g] s s1)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    (accC t S).pre (s1.callEntry.withRegions [pR (pa s g)] [pR (pa s f)]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := accChk_spec hc
  obtain ⟨e1, e2⟩ := argsIn2 hA
  have hD : 8 ≤ D := by omega
  have hwf := ce_wfS (ws := [64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s g)] [pR (pa s f)]
  sig_pre [accSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, A.red' i1 hD rf,
    A.red' i2 hD rg⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [pR (pa s f), pR (pa s g)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem accAt_ok {t : Poly → Poly → Poly} {n : String} {c : Prog isa} (C : Callee (fun S => accC t S) D c)
    {s : State} (L : Lay D rbs wbs s) {f g : Ptr} (hc : accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (callP n c [.ptr f, .ptr g]) s fun s' => PPostB D s s' [(f, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  obtain ⟨w1, i1, i2, _, ok⟩ := accChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (callP_ok C.ver.1 C.nosp C.depth L.dsm ok
    (fun s1 hA hm k => accPre C.hS (At.of L hm k) hc hA rf rg)
    (Covers.append_left (L.cR i2) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2⟩ := argsIn2 hA
  sig_post [accSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, Arg.val, hm₂, A.poly' i1 hD, A.poly' i2 hD] at hq
  exact hq

theorem accAt_tr {t : Poly → Poly → Poly} {n : String} {c : Prog isa} (C : Callee (fun S => accC t S) D c)
    {f g : Ptr} (hc : accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (callP n c [.ptr f, .ptr g]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, ok⟩ := accChk_spec hc
  refine callP_tr C.ver.1 C.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rfx, rgx⟩, ⟨rfy, rgy⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, accPre C.hS (At.of R.lx hmx kx) hc hAx rfx rgx, accPre C.hS (At.of R.ly hmy ky) hc hAy rfy rgy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i2) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i2) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2⟩ := argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := argsIn2 hAy
  sig_pub [accSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hy1, hy2, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

theorem addAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f g : Ptr}
    (hc : accChk (rbs ++ wbs) wbs f g = true) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (addAt P f g) s fun s' => PPostB D s s' [(f, 1024)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (pa s f) (add (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  accAt_ok (t := add) hP.add L hc rf rg

theorem subAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f g : Ptr}
    (hc : accChk (rbs ++ wbs) wbs f g = true) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (subAt P f g) s fun s' => PPostB D s s' [(f, 1024)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (pa s f) (sub (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  accAt_ok (t := sub) hP.sub L hc rf rg

theorem addAt_tr {P : Prims} (hP : PrimsOk P D) {f g : Ptr} (hc : accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (addAt P f g) fun _ _ => True :=
  accAt_tr (t := add) hP.add hc

theorem subAt_tr {P : Prims} (hP : PrimsOk P D) {f g : Ptr} (hc : accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (subAt P f g) fun _ _ => True :=
  accAt_tr (t := sub) hP.sub hc

/-! ## `RejNTTPoly` -/

/-- What a call of `vg_mldsa_rej_ntt_poly` to `a` needs of the layout. -/
def rejChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  inB wbs a 1024 && inB wbs (sc oPS) 2048 && inB bs (sc oRS) 34 && inB bs a 1024 && inB bs (sc oPS) 2048 &&
    sepB bs (sc oRS) 34 a 1024 && sepB bs (sc oRS) 34 (sc oPS) 2048 && sepB bs a 1024 (sc oPS) 2048 &&
    decide (a.1 ∈ bases) && decide (a.2 < 2 ^ 31)

theorem rejChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : rejChk bs wbs a = true) :
    inB wbs a 1024 = true ∧ inB wbs (sc oPS) 2048 = true ∧ inB bs (sc oRS) 34 = true ∧ inB bs a 1024 = true ∧
      inB bs (sc oPS) 2048 = true ∧ sepB bs (sc oRS) 34 a 1024 = true ∧ sepB bs (sc oRS) 34 (sc oPS) 2048 = true ∧
      sepB bs a 1024 (sc oPS) 2048 = true ∧ ([Arg.ptr (sc oRS), .ptr a, .ptr (sc oPS)].all Arg.ok) = true := by
  simp only [rejChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  simp only [List.all_cons, List.all_nil, Arg.ok, h9, h10, decide_true, Bool.and_true]
  decide

theorem rejPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {a : Ptr}
    (hc : rejChk (rbs ++ wbs) wbs a = true) (hA : ArgsIn [.ptr (sc oRS), .ptr a, .ptr (sc oPS)] s s1) :
    (rejNTTContract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s (sc oRS), 34⟩] [pR (pa s a), ⟨pa s (sc oPS), 2048⟩]) := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := rejChk_spec hc
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := ce_wfS (ws := [64, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨pa s (sc oRS), 34⟩]
    [pR (pa s a), ⟨pa s (sc oPS), 2048⟩]
  sig_pre [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_,
    A.L.nwp i1, A.L.nwp i2, A.L.nwp i3⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, conj_stk [⟨pa s (sc oRS), 34⟩, pR (pa s a), ⟨pa s (sc oPS), 2048⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

/-- The call of `vg_mldsa_rej_ntt_poly`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds`. -/
theorem rejCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {a : Ptr}
    (hc : rejChk (rbs ++ wbs) wbs a = true) :
    WP isa (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)]) s fun s' =>
      PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)) ((s'.gpr .rax).setWidth 32)
        (polyAt s'.mem (pa s a)) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := rejChk_spec hc
  have hD : 8 ≤ D := by have := hP.rejNTT.hS; omega
  refine WP.mono (callP_ok (hv_with hP.rejNTT.ver.1 hP.rejMax) hP.rejNTT.nosp hP.rejNTT.depth L.dsm ok
    (fun s1 hA hm k => rejPre hP.rejNTT.hS (At.of L hm k) hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, Arg.val, hm₂, er, A.bytes' i1 hD] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    e1, Arg.val, er, A.bytes i1 hD] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem rejCall_tr {P : Prims} (hP : PrimsOk P D) {a : Ptr} (hc : rejChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34)
      (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)])
      fun x y => (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := rejChk_spec hc
  have hD : 8 ≤ D := by have := hP.rejNTT.hS; omega
  refine callPRet_tr hP.rejNTT.ver.1 hP.rejRet ok
    fun x y x1 y1 ⟨R, hb⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, rejPre hP.rejNTT.hS (At.of R.lx hmx kx) hc hAx, rejPre hP.rejNTT.hS (At.of R.ly hmy ky) hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  have Ax := At.of R.lx hmx kx
  have Ay := At.of R.ly hmy ky
  sig_pub [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, Ax.bytes' i1 hD, Ay.bytes' i1 hD, hb]
  simp only [Ax.rsp, Ay.rsp, R.rsp, R.pa i1, R.pa i2, R.pa i3, and_self]

/-! ## `RejNTTPoly` four times -/

/-- What the call of `vg_mldsa_rej_ntt_poly4` from the seeds at `RS4` to the four polynomials from `a`,
with the working space `w`, needs of the layout. -/
def rej4Chk (bs wbs : List (Reg × Nat)) (a w : Ptr) : Bool :=
  inB wbs a 4096 && inB wbs w 8192 && inB bs (sc oRS4) 136 && inB bs a 4096 && inB bs w 8192 &&
    sepB bs (sc oRS4) 136 a 4096 && sepB bs (sc oRS4) 136 w 8192 && sepB bs a 4096 w 8192 &&
    decide (a.1 ∈ bases) && decide (a.2 < 2 ^ 31) && decide (w.1 ∈ bases) && decide (w.2 < 2 ^ 31)

theorem rej4Chk_spec {bs wbs : List (Reg × Nat)} {a w : Ptr} (hc : rej4Chk bs wbs a w = true) :
    inB wbs a 4096 = true ∧ inB wbs w 8192 = true ∧ inB bs (sc oRS4) 136 = true ∧ inB bs a 4096 = true ∧
      inB bs w 8192 = true ∧ sepB bs (sc oRS4) 136 a 4096 = true ∧ sepB bs (sc oRS4) 136 w 8192 = true ∧
      sepB bs a 4096 w 8192 = true ∧ ([Arg.ptr (sc oRS4), .ptr a, .ptr w].all Arg.ok) = true := by
  simp only [rej4Chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  simp only [List.all_cons, List.all_nil, Arg.ok, h9, h10, h11, h12, decide_true, Bool.and_true]
  decide

theorem rej4Pre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {a w : Ptr}
    (hc : rej4Chk (rbs ++ wbs) wbs a w = true) (hA : ArgsIn [.ptr (sc oRS4), .ptr a, .ptr w] s s1) :
    (rejNTT4Contract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s (sc oRS4), 136⟩] [⟨pa s a, 4096⟩, ⟨pa s w, 8192⟩]) := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := rej4Chk_spec hc
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := ce_wfS (ws := [64, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨pa s (sc oRS4), 136⟩]
    [⟨pa s a, 4096⟩, ⟨pa s w, 8192⟩]
  sig_pre [rejNTT4Contract, rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_,
    A.L.nwp i1, A.L.nwp i2, A.L.nwp i3⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, conj_stk [⟨pa s (sc oRS4), 136⟩, ⟨pa s a, 4096⟩, ⟨pa s w, 8192⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

/-- The seeds on entry to the call are those before it. -/
theorem At.seeds4 {s s1 : State} (A : At D rbs wbs s s1) (hi : inB (rbs ++ wbs) (sc oRS4) 136 = true) (hD : 8 ≤ D)
    {k : Nat} (hk : k < 4) :
    seed4 (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (pa s (sc oRS4)) k = seed4 s.mem (pa s (sc oRS4)) k := by
  unfold seed4
  rw [← VG.Proof.MlKem.bytesAt_slice _ _ (show 34 * k + 34 ≤ 136 by omega),
    ← VG.Proof.MlKem.bytesAt_slice s.mem _ (show 34 * k + 34 ≤ 136 by omega), A.bytes' hi hD]

/-- The call of `vg_mldsa_rej_ntt_poly4`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds` on each seed. -/
theorem rej4Call_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {a w : Ptr}
    (hc : rej4Chk (rbs ++ wbs) wbs a w = true) :
    WP isa (callP ("vg_mldsa_rej_ntt_poly4" ++ P.sfx) P.rej4 [.ptr (sc oRS4), .ptr a, .ptr w]) s fun s' =>
      PPostB D s s' [(a, 4096), (w, 8192)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4, Reduced s'.mem (poly4 (pa s a) k)) ∧
      (((s'.gpr .rax).setWidth 32 = 1 ∧ ∀ k < 4, ∃ b : Bounds,
          rejNTTPoly b.rejNTT (seed4 s.mem (pa s (sc oRS4)) k) = some (polyAt s'.mem (poly4 (pa s a) k))) ∨
        ((s'.gpr .rax).setWidth 32 = 0 ∧ ∃ k < 4,
          rejNTTPoly minBounds.rejNTT (seed4 s.mem (pa s (sc oRS4)) k) = none)) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4,
        (rejNTTPoly maxBounds.rejNTT (seed4 s.mem (pa s (sc oRS4)) k)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := rej4Chk_spec hc
  have hD : 8 ≤ D := by have := hP.rej4.hS; omega
  refine WP.mono (callP_ok (hv_with hP.rej4.ver.1 hP.rej4Max) hP.rej4.nosp hP.rej4.depth L.dsm ok
    (fun s1 hA hm k => rej4Pre hP.rej4.hS (At.of L hm k) hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [rejNTT4Contract, rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, Arg.val, hm₂, er] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    e1, Arg.val, er] at hx
  obtain ⟨hr, ho⟩ := hq
  refine ⟨hr, ?_, fun h1 k hk => by rw [← A.seeds4 i1 hD hk]; exact hx h1 k hk⟩
  rcases ho with ⟨h1, hb⟩ | ⟨h0, k, hk, hn⟩
  · exact .inl ⟨h1, fun k hk => by rw [← A.seeds4 i1 hD hk]; exact hb k hk⟩
  · exact .inr ⟨h0, k, hk, by rw [← A.seeds4 i1 hD hk]; exact hn⟩

theorem rej4Call_tr {P : Prims} (hP : PrimsOk P D) {a w : Ptr} (hc : rej4Chk (rbs ++ wbs) wbs a w = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧
        bytesAt x.mem (pa x (sc oRS4)) 136 = bytesAt y.mem (pa y (sc oRS4)) 136)
      (callP ("vg_mldsa_rej_ntt_poly4" ++ P.sfx) P.rej4 [.ptr (sc oRS4), .ptr a, .ptr w])
      fun x y => (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := rej4Chk_spec hc
  have hD : 8 ≤ D := by have := hP.rej4.hS; omega
  refine callPRet_tr hP.rej4.ver.1 hP.rej4Ret ok
    fun x y x1 y1 ⟨R, hb⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, rej4Pre hP.rej4.hS (At.of R.lx hmx kx) hc hAx, rej4Pre hP.rej4.hS (At.of R.ly hmy ky) hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  have Ax := At.of R.lx hmx kx
  have Ay := At.of R.ly hmy ky
  sig_pub [rejNTT4Contract, rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, Ax.bytes' i1 hD, Ay.bytes' i1 hD, hb]
  simp only [Ax.rsp, Ay.rsp, R.rsp, R.pa i1, R.pa i2, R.pa i3, and_self]

/-! ## `ExpandMask` -/

/-- What a call of `vg_mldsa_expand_mask_poly` to `a` needs of the layout. -/
def maskChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  inB wbs a 1024 && inB wbs (sc oPS) 2048 && inB bs (sc oMS) 66 && inB bs a 1024 && inB bs (sc oPS) 2048 &&
    sepB bs (sc oMS) 66 a 1024 && sepB bs (sc oMS) 66 (sc oPS) 2048 && sepB bs a 1024 (sc oPS) 2048 &&
    decide (a.1 ∈ bases) && decide (a.2 < 2 ^ 31)

theorem maskChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : maskChk bs wbs a = true) :
    inB wbs a 1024 = true ∧ inB wbs (sc oPS) 2048 = true ∧ inB bs (sc oMS) 66 = true ∧ inB bs a 1024 = true ∧
      inB bs (sc oPS) 2048 = true ∧ sepB bs (sc oMS) 66 a 1024 = true ∧ sepB bs (sc oMS) 66 (sc oPS) 2048 = true ∧
      sepB bs a 1024 (sc oPS) 2048 = true ∧ a.1 ∈ bases ∧ a.2 < 2 ^ 31 := by
  simp only [maskChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem maskPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : maskChk (rbs ++ wbs) wbs a = true)
    (hA : ArgsIn [.ptr (sc oMS), .imm γ, .ptr a, .ptr (sc oPS)] s s1) :
    (expandMaskContract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s (sc oMS), 66⟩] [pR (pa s a), ⟨pa s (sc oPS), 2048⟩]) := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := maskChk_spec hc
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  have hD : 8 ≤ D := by omega
  have hγ' : γ < 2 ^ 32 := by omega
  have hwf := ce_wfS (ws := [64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨pa s (sc oMS), 66⟩]
    [pR (pa s a), ⟨pa s (sc oPS), 2048⟩]
  sig_pre [expandMaskContract, expandMaskSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, Arg.val, sw32_ofNat hγ']
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_,
    A.L.nwp i1, A.L.nwp i2, A.L.nwp i3, hγ⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, conj_stk [⟨pa s (sc oMS), 66⟩, pR (pa s a), ⟨pa s (sc oPS), 2048⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

theorem maskAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : maskChk (rbs ++ wbs) wbs a = true) :
    WP isa (maskAt P γ a) s fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s (sc oMS)) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1⟩ := maskChk_spec hc
  have hD : 8 ≤ D := by have := hP.expandMask.hS; omega
  have hγ' : γ < 2 ^ 32 := by omega
  refine WP.mono (callP_ok hP.expandMask.ver.1 hP.expandMask.nosp hP.expandMask.depth L.dsm
    (by simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true, decide_eq_true hγ']; decide)
    (fun s1 hA hm k => maskPre hP.expandMask.hS (At.of L hm k) hγ hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, _⟩ := argsIn4 hA
  sig_post [expandMaskContract, expandMaskSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, A.bytes' i1 hD, sw32_ofNat hγ'] at hq
  exact hq

theorem maskAt_tr {P : Prims} (hP : PrimsOk P D) {γ : Nat} {a : Ptr} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19)
    (hc : maskChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (LRel D rbs wbs) (maskAt P γ a) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1⟩ := maskChk_spec hc
  have hγ' : γ < 2 ^ 32 := by omega
  refine callP_tr hP.expandMask.ver.1 hP.expandMask.ver.2.1
    (by simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true, decide_eq_true hγ']; decide)
    fun x y x1 y1 R ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, maskPre hP.expandMask.hS (At.of R.lx hmx kx) hγ hc hAx,
        maskPre hP.expandMask.hS (At.of R.ly hmy ky) hγ hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := argsIn4 hAy
  sig_pub [expandMaskContract, expandMaskSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `SampleInBall` -/

/-- What a call of `vg_mldsa_sample_in_ball` of the `len` bytes at `CT` to `c` needs of the layout. -/
def ballChk (bs wbs : List (Reg × Nat)) (len : Nat) (c : Ptr) : Bool :=
  inB wbs c 1024 && inB wbs (sc oPS) 2048 && inB bs (sc oCT) len && inB bs c 1024 && inB bs (sc oPS) 2048 &&
    sepB bs (sc oCT) len c 1024 && sepB bs (sc oCT) len (sc oPS) 2048 && sepB bs c 1024 (sc oPS) 2048 &&
    decide (c.1 ∈ bases) && decide (c.2 < 2 ^ 31)

theorem ballChk_spec {bs wbs : List (Reg × Nat)} {len : Nat} {c : Ptr} (hc : ballChk bs wbs len c = true) :
    inB wbs c 1024 = true ∧ inB wbs (sc oPS) 2048 = true ∧ inB bs (sc oCT) len = true ∧ inB bs c 1024 = true ∧
      inB bs (sc oPS) 2048 = true ∧ sepB bs (sc oCT) len c 1024 = true ∧ sepB bs (sc oCT) len (sc oPS) 2048 = true ∧
      sepB bs c 1024 (sc oPS) 2048 = true ∧ c.1 ∈ bases ∧ c.2 < 2 ^ 31 := by
  simp only [ballChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem ballArgs_ok {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams) (b1 : c.1 ∈ bases)
    (o1 : c.2 < 2 ^ 31) : [Arg.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)].all Arg.ok = true := by
  have : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true, decide_eq_true this.1,
    decide_eq_true this.2]
  decide

theorem ballPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : ballChk (rbs ++ wbs) wbs len c = true)
    (hA : ArgsIn [.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)] s s1) :
    (sampleInBallContract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s (sc oCT), len⟩] [pR (pa s c), ⟨pa s (sc oPS), 2048⟩]) := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := ballChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  have hD : 8 ≤ D := by omega
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  have hwf := ce_wfS (ws := [64, 64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨pa s (sc oCT), len⟩]
    [pR (pa s c), ⟨pa s (sc oPS), 2048⟩]
  sig_pre [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, sw32_ofNat hl.2, toNat64 hl.1]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_,
    A.L.nwp i1, A.L.nwp i2, A.L.nwp i3, hp⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, conj_stk [⟨pa s (sc oCT), len⟩, pR (pa s c), ⟨pa s (sc oPS), 2048⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

/-- The call of `vg_mldsa_sample_in_ball`: its outcome, and that it succeeds
only if `SampleInBall` finishes within `maxBounds`. -/
theorem ballCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : ballChk (rbs ++ wbs) wbs len c = true) :
    WP isa (ballAt P len tau c) s fun s' =>
      PPostB D s s' [(c, 1024), (sc oPS, 2048)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → Reduced s'.mem (pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (pa s (sc oCT)) len)).map toRq)
        ((s'.gpr .rax).setWidth 32) (polyAt s'.mem (pa s c)) ∧
      ((s'.gpr .rax).setWidth 32 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (pa s (sc oCT)) len)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1⟩ := ballChk_spec hc
  have hD : 8 ≤ D := by have := hP.ball.hS; omega
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  refine WP.mono (callP_ok (hv_with hP.ball.ver.1 hP.ballMax) hP.ball.nosp hP.ball.depth L.dsm (ballArgs_ok hp b1 o1)
    (fun s1 hA hm k => ballPre hP.ball.hS (At.of L hm k) hp hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4, _⟩ := argsIn5 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, Arg.val, hm₂, er, sw32_ofNat hl.2, toNat64 hl.1, A.bytes' i1 hD] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    e1, e2, e3, Arg.val, er, sw32_ofNat hl.2, toNat64 hl.1, A.bytes i1 hD] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem ballCall_tr {P : Prims} (hP : PrimsOk P D) {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams)
    (hc : ballChk (rbs ++ wbs) wbs len c = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oCT)) len = bytesAt y.mem (pa y (sc oCT)) len)
      (ballAt P len tau c) fun x y => (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1, o1⟩ := ballChk_spec hc
  have hD : 8 ≤ D := by have := hP.ball.hS; omega
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  refine callPRet_tr hP.ball.ver.1 hP.ballRet (ballArgs_ok hp b1 o1)
    fun x y x1 y1 ⟨R, hb⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, ballPre hP.ball.hS (At.of R.lx hmx kx) hp hc hAx, ballPre hP.ball.hS (At.of R.ly hmy ky) hp hc hAy,
        ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
        by rw [kx.2.2]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
        by rw [ky.2.2]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := argsIn5 hAx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := argsIn5 hAy
  have Ax := At.of R.lx hmx kx
  have Ay := At.of R.ly hmy ky
  sig_pub [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hy1, hy2, hy3, hy4, hy5, Arg.val, toNat64 hl.1, Ax.bytes' i1 hD,
    Ay.bytes' i1 hD, hb]
  simp only [Ax.rsp, Ay.rsp, R.rsp, R.pa i1, R.pa i2, R.pa i3, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign
