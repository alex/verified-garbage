import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Prims

/-!
# ML-DSA signing on ARMv7: calls of the rounding functions, the norm check and `SimpleBitPack`

Untrusted: everything here is checked by Lean. As `Prims.lean`, for
`vg_mldsa_high_bits`, `vg_mldsa_low_bits`, `vg_mldsa_norm_lt`,
`vg_mldsa_make_hint` and `vg_mldsa_simple_bit_pack`.
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (setWidth_append32)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-- What a call with a buffer `f` of `lf` bytes read and a buffer `out` of
`l` bytes written needs of the layout. -/
def rwChk (bs wbs : List (Reg × Nat)) (f : Ptr) (lf : Nat) (out : Ptr) (l : Nat) : Bool :=
  inB wbs out l && inB bs f lf && inB bs out l && sepB bs f lf out l && decide (f.1 ∈ bases) &&
    decide (out.1 ∈ bases)

theorem rwChk_spec {bs wbs : List (Reg × Nat)} {f out : Ptr} {lf l : Nat} (hc : rwChk bs wbs f lf out l = true) :
    inB wbs out l = true ∧ inB bs f lf = true ∧ inB bs out l = true ∧ sepB bs f lf out l = true ∧
      f.1 ∈ bases ∧ out.1 ∈ bases := by
  simp only [rwChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem gamma2_lt {γ : Nat} (h : γ ∈ gamma2s) : γ < 2 ^ 32 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

/-! ## `HighBits` and `LowBits` -/

/-- The contract of `vg_mldsa_high_bits` or `vg_mldsa_low_bits`: `bitsSig`'s,
with the postcondition `Q`. -/
abbrev bitsC (Q : Nat → Poly → Mem → Addr → Prop) (S : Nat) : Contract isa :=
  bitsSig.contract Arm.abi
    (pre := fun r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun r gamma2 out m m' _ => Q gamma2.toNat (polyAt m r) m' out)
    (writeArgs := true)
    (stack := S)

theorem bitsPre {Q : Nat → Poly → Mem → Addr → Prop} {S : Nat} {s E : State} (En : Ent D rbs wbs s S E)
    {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true)
    (g0 : E.gpr .r0 = s.gpr r.1 + BitVec.ofNat 32 r.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 γ)
    (g2 : E.gpr .r2 = s.gpr out.1 + BitVec.ofNat 32 out.2) (hrd : E.rd = [pR (pa s r)])
    (hwr : E.wr = [pR (pa s out)]) (hr : Reduced s.mem (pa s r)) :
    (bitsC Q S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  sig_pre [bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, En.L.w i1 (by decide), En.L.w i2 (by decide), toNat32 (gamma2_lt hγ)]
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.conj (bs := [(r, 1024), (out, 1024)]) (by simp [i1, i2]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), hγ, En.red i1 hr⟩

theorem bitsArgs_ok {r out : Ptr} {γ : Nat} (b1 : r.1 ∈ bases) (b2 : out.1 ∈ bases) :
    [Arg.ptr r, .imm γ, .ptr out].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem bitsAt_ok {Q : Nat → Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : Callee (fun S => bitsC Q S) 0 D c) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (callR n c [.ptr r, .imm γ, .ptr out]) s fun s' => PPostB D s s' [(out, 1024)] ∧ CS s s' ∧
      Q γ (polyAt s.mem (pa s r)) s'.mem (pa s out) := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  refine WP.mono (callR_ok C.ver.1 (by have := C.su; have := C.hS; omega) (bitsArgs_ok b1 b2) L.sp
    (rd := [pR (pa s r)]) (wr := [pR (pa s out)])
    (fun s1 hA k => bitsPre (ent_R L k (by have := C.hS; omega) _ _) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hA).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hA).2.2) rfl rfl hr)
    (covers_append (L.cR i1) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  sig_post [bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, Arg.val, k.mem, toNat32 (gamma2_lt hγ), L.w i1 (by decide), L.w i2 (by decide)] at hq
  exact hq

theorem bitsAt_tr {Q : Nat → Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : Callee (fun S => bitsC Q S) 0 D c) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (callR n c [.ptr r, .imm γ, .ptr out]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  have hS : C.S ≤ D := by have := C.hS; omega
  refine callR_tr C.ver.1 C.ver.2.1 (bitsArgs_ok b1 b2) fun x y x1 y1 ⟨R, rx, ry⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, bitsPre (ent_R R.lx kx hS [pR (pa x r)] [pR (pa x out)]) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAx).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAx).2.2) rfl rfl rx,
      bitsPre (ent_R R.ly ky hS [pR (pa y r)] [pR (pa y out)]) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAy).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAy).2.2) rfl rfl ry, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append (R.lx.cR i1) (covers_wr (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact covers_append (R.ly.cR i1) (covers_wr (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  sig_pub [bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

theorem highBitsAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (highBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧ CS s s' ∧
      NatPolyIs s'.mem (pa s out) ((polyAt s.mem (pa s r)).map fun c => (highBits γ c).toNat) :=
  bitsAt_ok (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) hP.highBits L hγ hc hr

theorem highBitsAt_tr {P : Prims} (hP : PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (highBitsAt P r γ out) fun _ _ => True :=
  bitsAt_tr (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) hP.highBits hγ hc

theorem lowBitsAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (lowBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s out) ((polyAt s.mem (pa s r)).map fun c => ofInt (lowBits γ c)) :=
  bitsAt_ok (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (lowBits γ c))) hP.lowBits L hγ hc hr

theorem lowBitsAt_tr {P : Prims} (hP : PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (lowBitsAt P r γ out) fun _ _ => True :=
  bitsAt_tr (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (lowBits γ c))) hP.lowBits hγ hc

/-! ## Norms -/

/-- What a call of `vg_mldsa_norm_lt` on `f` needs of the layout. -/
def normChk (bs : List (Reg × Nat)) (f : Ptr) : Bool :=
  inB bs f 1024 && decide (f.1 ∈ bases)

theorem normPre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {f : Ptr}
    (hc : normChk (rbs ++ wbs) f = true) (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2)
    (hrd : E.rd = [pR (pa s f)]) (hwr : E.wr = []) (hr : Reduced s.mem (pa s f)) :
    (normLtContract Arm.abi S).pre E := by
  simp only [normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨i1, _⟩ := hc
  sig_pre [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, En.L.w i1 (by decide)]
  exact ⟨wf0 En.wf, hrd, hwr, En.conj (bs := [(f, 1024)]) (by simp [i1]), En.L.fit i1 (by decide), En.red i1 hr⟩

theorem normArgs_ok {bs : List (Reg × Nat)} {f : Ptr} {B : Nat} (hc : normChk bs f = true) : [Arg.ptr f, .imm B].all Arg.ok = true := by
  simp only [normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp [Arg.ok, hc.2]

theorem normCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f : Ptr} {B : Nat}
    (hB : B < 2 ^ 32) (hc : normChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (callR "vg_mldsa_norm_lt" P.normLt [.ptr f, .imm B]) s fun s' => PPostB D s s' [] ∧ CS s s' ∧
      s'.gpr .r0 = if normRq [polyAt s.mem (pa s f)] < B then 1 else 0 := by
  have i1 : inB (rbs ++ wbs) f 1024 = true := by
    simp only [normChk, Bool.and_eq_true] at hc; exact hc.1
  refine WP.mono (callR_ok hP.normLt.ver.1 (by have := hP.normLt.su; have := hP.normLt.hS; omega)
    (normArgs_ok hc) L.sp (rd := [pR (pa s f)]) (wr := [])
    (fun s1 hA k => normPre (ent_R L k (by have := hP.normLt.hS; omega) _ _) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hA).1) rfl rfl hr)
    (covers_append (L.cR i1) covers_nil) covers_nil)
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2⟩ := argsIn2 hA
  sig_post [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, Arg.val, k.mem, setWidth_append32, toNat32 hB, L.w i1 (by decide)] at hq
  exact hq

theorem normCall_tr {P : Prims} (hP : PrimsOk P D) {f : Ptr} {B : Nat} (hc : normChk (rbs ++ wbs) f = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f))
      (callR "vg_mldsa_norm_lt" P.normLt [.ptr f, .imm B]) fun _ _ => True := by
  have i1 : inB (rbs ++ wbs) f 1024 = true := by
    simp only [normChk, Bool.and_eq_true] at hc; exact hc.1
  have hS : hP.normLt.S ≤ D := by have := hP.normLt.hS; omega
  refine callR_tr hP.normLt.ver.1 hP.normLt.ver.2.1 (normArgs_ok hc) fun x y x1 y1 ⟨R, rx, ry⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, normPre (ent_R R.lx kx hS [pR (pa x f)] []) hc (by rw [vR _ _ _ nl0]; exact (argsIn2 hAx).1)
      rfl rfl rx,
      normPre (ent_R R.ly ky hS [pR (pa y f)] []) hc (by rw [vR _ _ _ nl0]; exact (argsIn2 hAy).1) rfl rfl ry, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append (R.lx.cR i1) covers_nil, covers_nil,
      by rw [ky.rd, ky.wr]; exact covers_append (R.ly.cR i1) covers_nil, covers_nil⟩
  obtain ⟨hx1, hx2⟩ := argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := argsIn2 hAy
  sig_pub [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hy1, hy2, Arg.val, R.eq i1, R.sp, and_self]

/-! ## `MakeHint` -/

/-- What a call of `vg_mldsa_make_hint` on `z`, `r` to `h` needs of the layout. -/
def hintChk (bs wbs : List (Reg × Nat)) (z r h : Ptr) : Bool :=
  inB wbs h 1024 && inB bs z 1024 && inB bs r 1024 && inB bs h 1024 && sepB bs z 1024 h 1024 &&
    sepB bs r 1024 h 1024 && decide (z.1 ∈ bases) && decide (r.1 ∈ bases) && decide (h.1 ∈ bases)

theorem hintChk_spec {bs wbs : List (Reg × Nat)} {z r h : Ptr} (hc : hintChk bs wbs z r h = true) :
    inB wbs h 1024 = true ∧ inB bs z 1024 = true ∧ inB bs r 1024 = true ∧ inB bs h 1024 = true ∧
      sepB bs z 1024 h 1024 = true ∧ sepB bs r 1024 h 1024 = true ∧ z.1 ∈ bases ∧ r.1 ∈ bases ∧ h.1 ∈ bases := by
  simp only [hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem hintArgs_ok {z r h : Ptr} {γ : Nat} (b1 : z.1 ∈ bases) (b2 : r.1 ∈ bases) (b3 : h.1 ∈ bases) :
    [Arg.ptr z, .ptr r, .imm γ, .ptr h].all Arg.ok = true := by
  simp [Arg.ok, b1, b2, b3]

theorem hintPre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : hintChk (rbs ++ wbs) wbs z r h = true)
    (g0 : E.gpr .r0 = s.gpr z.1 + BitVec.ofNat 32 z.2) (g1 : E.gpr .r1 = s.gpr r.1 + BitVec.ofNat 32 r.2)
    (g2 : E.gpr .r2 = BitVec.ofNat 32 γ) (g3 : E.gpr .r3 = s.gpr h.1 + BitVec.ofNat 32 h.2)
    (hrd : E.rd = [pR (pa s z), pR (pa s r)]) (hwr : E.wr = [pR (pa s h)])
    (rz : Reduced s.mem (pa s z)) (rr : Reduced s.mem (pa s r)) :
    (makeHintContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, i3, d13, d23, _⟩ := hintChk_spec hc
  sig_pre [makeHintContract, makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.L.w i1 (by decide), En.L.w i2 (by decide), En.L.w i3 (by decide),
    toNat32 (gamma2_lt hγ)]
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d13, En.L.disj d23,
    En.conj (bs := [(z, 1024), (r, 1024), (h, 1024)]) (by simp [i1, i2, i3]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), En.L.fit i3 (by decide), hγ, En.red i1 rz, En.red i2 rr⟩

theorem hintCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : hintChk (rbs ++ wbs) wbs z r h = true) (rz : Reduced s.mem (pa s z))
    (rr : Reduced s.mem (pa s r)) :
    WP isa (callR "vg_mldsa_make_hint" P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) s fun s' =>
      PPostB D s s' [(h, 1024)] ∧ CS s s' ∧
      HintIs s'.mem (pa s h) 1 [Vector.zipWith (makeHint γ) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] ∧
      (s'.gpr .r0).toNat =
        hintOnes [Vector.zipWith (makeHint γ) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] := by
  obtain ⟨w1, i1, i2, i3, _, _, b1, b2, b3⟩ := hintChk_spec hc
  refine WP.mono (callR_ok hP.makeHint.ver.1 (by have := hP.makeHint.su; have := hP.makeHint.hS; omega)
    (hintArgs_ok b1 b2 b3) L.sp (rd := [pR (pa s z), pR (pa s r)]) (wr := [pR (pa s h)])
    (fun s1 hA k => hintPre (ent_R L k (by have := hP.makeHint.hS; omega) _ _) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hA).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hA).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hA).2.2.2) rfl rfl rz rr)
    (covers_append (covers_cons (L.cR i1) (L.cR i2)) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  sig_post [makeHintContract, makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, e4, Arg.val, k.mem, setWidth_append32, toNat32 (gamma2_lt hγ), L.w i1 (by decide),
    L.w i2 (by decide), L.w i3 (by decide)] at hq
  exact hq

theorem hintCall_tr {P : Prims} (hP : PrimsOk P D) {z r h : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : hintChk (rbs ++ wbs) wbs z r h = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x z) ∧ Reduced x.mem (pa x r)) ∧
      (Reduced y.mem (pa y z) ∧ Reduced y.mem (pa y r)))
      (callR "vg_mldsa_make_hint" P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, b1, b2, b3⟩ := hintChk_spec hc
  have hS : hP.makeHint.S ≤ D := by have := hP.makeHint.hS; omega
  refine callR_tr hP.makeHint.ver.1 hP.makeHint.ver.2.1 (hintArgs_ok b1 b2 b3)
    fun x y x1 y1 ⟨R, ⟨rzx, rrx⟩, ⟨rzy, rry⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, hintPre (ent_R R.lx kx hS [pR (pa x z), pR (pa x r)] [pR (pa x h)]) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hAx).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hAx).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hAx).2.2.2) rfl rfl
      rzx rrx,
      hintPre (ent_R R.ly ky hS [pR (pa y z), pR (pa y r)] [pR (pa y h)]) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hAy).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hAy).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hAy).2.2.2) rfl rfl
      rzy rry, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append (covers_cons (R.lx.cR i1) (R.lx.cR i2)) (covers_wr (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact covers_append (covers_cons (R.ly.cR i1) (R.ly.cR i2)) (covers_wr (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := argsIn4 hAy
  sig_pub [makeHintContract, makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.eq i1, R.eq i2, R.eq i3, R.sp,
    and_self]

/-! ## `SimpleBitPack` -/

theorem sbpArgs_ok {f out : Ptr} {b len : Nat} (b1 : f.1 ∈ bases) (b2 : out.1 ∈ bases) :
    [Arg.ptr f, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem sbp_lt {b len : Nat} (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) :
    b < 2 ^ 32 ∧ len < 2 ^ 32 ∧ 0 < len := by
  simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> subst hl <;> decide

theorem sbpPre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 b)
    (g2 : E.gpr .r2 = s.gpr out.1 + BitVec.ofNat 32 out.2) (g3 : E.gpr .r3 = BitVec.ofNat 32 len)
    (hrd : E.rd = [pR (pa s f)]) (hwr : E.wr = [⟨pa s out, len⟩])
    (hle : ∀ i < 256, (coeffAt s.mem (pa s f) i).toNat ≤ b) :
    (simpleBitPackContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨hb', hl', hl0⟩ := sbp_lt hb hl
  sig_pre [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.L.w i1 (by decide), En.L.w i2 hl0, toNat32 hb', toNat32 hl']
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.conj (bs := [(f, 1024), (out, len)]) (by simp [i1, i2]),
    En.L.fit i1 (by decide), En.L.fit i2 hl0, hb, hl, fun i hi => by rw [En.coeff i1 hi]; exact hle i hi⟩

theorem sbpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hle : ∀ i < 256, (coeffAt s.mem (pa s f) i).toNat ≤ b) :
    WP isa (simpleBitPackAt P f b out len) s fun s' => PPostB D s s' [(out, len)] ∧ CS s s' ∧
      bytesAt s'.mem (pa s out) len = simpleBitPack (natPolyAt s.mem (pa s f)) b := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  obtain ⟨hb', hl', hl0⟩ := sbp_lt hb hl
  refine WP.mono (callR_ok hP.simpleBitPack.ver.1 (by have := hP.simpleBitPack.su; have := hP.simpleBitPack.hS; omega)
    (sbpArgs_ok b1 b2) L.sp (rd := [pR (pa s f)]) (wr := [⟨pa s out, len⟩])
    (fun s1 hA k => sbpPre (ent_R L k (by have := hP.simpleBitPack.hS; omega) _ _) hb hl hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hA).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hA).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hA).2.2.2) rfl rfl hle)
    (covers_append (L.cR i1) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  sig_post [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, e4, Arg.val, k.mem, toNat32 hb', toNat32 hl', L.w i1 (by decide), L.w i2 hl0] at hq
  exact hq

theorem sbpAt_tr {P : Prims} (hP : PrimsOk P D) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (∀ i < 256, (coeffAt x.mem (pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (coeffAt y.mem (pa y f) i).toNat ≤ b)) (simpleBitPackAt P f b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  have hS : hP.simpleBitPack.S ≤ D := by have := hP.simpleBitPack.hS; omega
  refine callR_tr hP.simpleBitPack.ver.1 hP.simpleBitPack.ver.2.1 (sbpArgs_ok b1 b2)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, sbpPre (ent_R R.lx kx hS [pR (pa x f)] [⟨pa x out, len⟩]) hb hl hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hAx).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hAx).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hAx).2.2.2) rfl rfl rx,
      sbpPre (ent_R R.ly ky hS [pR (pa y f)] [⟨pa y out, len⟩]) hb hl hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hAy).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hAy).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hAy).2.2.2) rfl rfl ry, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append (R.lx.cR i1) (covers_wr (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact covers_append (R.ly.cR i1) (covers_wr (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := argsIn4 hAy
  sig_pub [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

end

end VG.Proof.MlDsa.Arm.Sign
