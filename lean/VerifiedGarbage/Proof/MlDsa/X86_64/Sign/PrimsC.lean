import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Prims

/-!
# ML-DSA signing on x86-64: calls of rounding, norms, hints and packing

Untrusted: everything here is checked by Lean. As `Prims.lean`, for
`vg_mldsa_high_bits`, `vg_mldsa_low_bits`, `vg_mldsa_norm_lt`,
`vg_mldsa_make_hint`, `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`,
`vg_mldsa_bit_unpack` and `vg_mldsa_hint_bit_pack`.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-- What a call with a polynomial `f` read and a buffer `out` of `l` bytes
written needs of the layout. -/
def rwChk (bs wbs : List (Reg × Nat)) (f : Ptr) (lf : Nat) (out : Ptr) (l : Nat) : Bool :=
  inB wbs out l && inB bs f lf && inB bs out l && sepB bs f lf out l && decide (f.1 ∈ bases) &&
    decide (f.2 < 2 ^ 31) && decide (out.1 ∈ bases) && decide (out.2 < 2 ^ 31)

theorem rwChk_spec {bs wbs : List (Reg × Nat)} {f out : Ptr} {lf l : Nat} (hc : rwChk bs wbs f lf out l = true) :
    inB wbs out l = true ∧ inB bs f lf = true ∧ inB bs out l = true ∧ sepB bs f lf out l = true ∧
      f.1 ∈ bases ∧ f.2 < 2 ^ 31 ∧ out.1 ∈ bases ∧ out.2 < 2 ^ 31 := by
  simp only [rwChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## `HighBits` and `LowBits` -/

theorem gamma2_lt {γ : Nat} (h : γ ∈ gamma2s) : γ < 2 ^ 32 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

theorem bitsArgs_ok {bs : List (Reg × Nat)} {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s) (hc : rwChk bs wbs r 1024 out 1024 = true) :
    [Arg.ptr r, .imm γ, .ptr out].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true (gamma2_lt hγ)]

/-- The contract of `vg_mldsa_high_bits` or `vg_mldsa_low_bits`: `bitsSig`'s,
with the postcondition `Q`. -/
abbrev bitsC (Q : Nat → Poly → Mem → Addr → Prop) (S : Nat) : Contract isa :=
  bitsSig.contract X86_64.abi
    (pre := fun r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun r gamma2 out m m' _ => Q gamma2.toNat (polyAt m r) m' out)
    (writeArgs := true)
    (stack := S)

theorem bitsPre {Q : Nat → Poly → Mem → Addr → Prop} {S : Nat} (hS : S + 8 ≤ D) {s s1 : State}
    (A : At D rbs wbs s s1) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hA : ArgsIn [.ptr r, .imm γ, .ptr out] s s1)
    (hr : Reduced s.mem (pa s r)) :
    (bitsC Q S).pre (s1.callEntry.withRegions [pR (pa s r)] [pR (pa s out)]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := ce_wfS (ws := [64, 32, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s r)] [pR (pa s out)]
  sig_pre [bitsSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val, sw32_ofNat (gamma2_lt hγ)]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hγ, A.red' i1 hD hr⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [pR (pa s r), pR (pa s out)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem bitsAt_ok {Q : Nat → Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : Callee (fun S => bitsC Q S) D c) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (callP n c [.ptr r, .imm γ, .ptr out]) s fun s' => PPostB D s s' [(out, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ Q γ (polyAt s.mem (pa s r)) s'.mem (pa s out) := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (callP_ok C.ver.1 C.nosp C.depth L.dsm (bitsArgs_ok hγ hc)
    (fun s1 hA hm k => bitsPre C.hS (At.of L hm k) hγ hc hA hr)
    (covers_append (L.cR i1) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  sig_post [bitsSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, A.poly' i1 hD, sw32_ofNat (gamma2_lt hγ)] at hq
  exact hq

theorem bitsAt_tr {Q : Nat → Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : Callee (fun S => bitsC Q S) D c) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (callP n c [.ptr r, .imm γ, .ptr out]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  refine callP_tr C.ver.1 C.ver.2.1 (bitsArgs_ok hγ hc)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, bitsPre C.hS (At.of R.lx hmx kx) hγ hc hAx rx, bitsPre C.hS (At.of R.ly hmy ky) hγ hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_append (R.lx.cR i1) (covers_wr (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact covers_append (R.ly.cR i1) (covers_wr (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  sig_pub [bitsSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

theorem highBitsAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (highBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      NatPolyIs s'.mem (pa s out) ((polyAt s.mem (pa s r)).map fun c => (highBits γ c).toNat) :=
  bitsAt_ok (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) hP.highBits L hγ hc hr

theorem highBitsAt_tr {P : Prims} (hP : PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (highBitsAt P r γ out) fun _ _ => True :=
  bitsAt_tr (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) hP.highBits hγ hc

theorem lowBitsAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (lowBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
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
  inB bs f 1024 && decide (f.1 ∈ bases) && decide (f.2 < 2 ^ 31)

theorem normPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {f : Ptr} {B : Nat}
    (hc : normChk (rbs ++ wbs) f = true) (hA : ArgsIn [.ptr f, .imm B] s s1)
    (hr : Reduced s.mem (pa s f)) :
    (normLtContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s f)] []) := by
  simp only [normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨i1, _⟩, _⟩ := hc
  obtain ⟨e1, e2⟩ := argsIn2 hA
  have hD : 8 ≤ D := by omega
  have hwf := ce_wfS (ws := [64, 32]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s f)] []
  sig_pre [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, Arg.val]
  refine ⟨hwf, trivial, ?_, A.L.nwp i1, A.red' i1 hD hr⟩
  refine Sig.conj_cons.mpr ⟨A.ret i1 hD, conj_stk [pR (pa s f)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
  exact A.stk hS i1

theorem normArgs_ok {bs : List (Reg × Nat)} {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : normChk bs f = true) :
    [Arg.ptr f, .imm B].all Arg.ok = true := by
  simp only [normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only [List.all_cons, List.all_nil, Arg.ok, hc.1.2, hc.2, decide_true, Bool.and_true, decide_eq_true hB]

theorem normCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f : Ptr} {B : Nat}
    (hB : B < 2 ^ 32) (hc : normChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (callP "vg_mldsa_norm_lt" P.normLt [.ptr f, .imm B]) s fun s' => PPostB D s s' [] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (s'.gpr .rax).setWidth 32 = if normRq [polyAt s.mem (pa s f)] < B then 1 else 0 := by
  have i1 : inB (rbs ++ wbs) f 1024 = true := by
    simp only [normChk, Bool.and_eq_true] at hc; exact hc.1.1
  have hD : 8 ≤ D := by have := hP.normLt.hS; omega
  refine WP.mono (callP_ok hP.normLt.ver.1 hP.normLt.nosp hP.normLt.depth L.dsm (normArgs_ok hB hc)
    (fun s1 hA hm k => normPre hP.normLt.hS (At.of L hm k) hc hA hr)
    (covers_append (L.cR i1) covers_nil) covers_nil)
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2⟩ := argsIn2 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, Arg.val, er, A.poly' i1 hD, sw32_ofNat hB] at hq
  exact hq

theorem normCall_tr {P : Prims} (hP : PrimsOk P D) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32)
    (hc : normChk (rbs ++ wbs) f = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f))
      (callP "vg_mldsa_norm_lt" P.normLt [.ptr f, .imm B]) fun _ _ => True := by
  have i1 : inB (rbs ++ wbs) f 1024 = true := by
    simp only [normChk, Bool.and_eq_true] at hc; exact hc.1.1
  refine callP_tr hP.normLt.ver.1 hP.normLt.ver.2.1 (normArgs_ok hB hc)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, normPre hP.normLt.hS (At.of R.lx hmx kx) hc hAx rx,
        normPre hP.normLt.hS (At.of R.ly hmy ky) hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_append (R.lx.cR i1) covers_nil, covers_nil,
        by rw [ky.2.1, ky.2.2]; exact covers_append (R.ly.cR i1) covers_nil, covers_nil,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2⟩ := argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := argsIn2 hAy
  sig_pub [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hy1, hy2, Arg.val, R.pa i1, (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp,
    and_self]

/-! ## `MakeHint` -/

/-- What a call of `vg_mldsa_make_hint` on `z`, `r` to `h` needs of the layout. -/
def hintChk (bs wbs : List (Reg × Nat)) (z r h : Ptr) : Bool :=
  inB wbs h 1024 && inB bs z 1024 && inB bs r 1024 && inB bs h 1024 && sepB bs z 1024 h 1024 &&
    sepB bs r 1024 h 1024 && decide (z.1 ∈ bases) && decide (z.2 < 2 ^ 31) && decide (r.1 ∈ bases) &&
    decide (r.2 < 2 ^ 31) && decide (h.1 ∈ bases) && decide (h.2 < 2 ^ 31)

theorem hintChk_spec {bs wbs : List (Reg × Nat)} {z r h : Ptr} (hc : hintChk bs wbs z r h = true) :
    inB wbs h 1024 = true ∧ inB bs z 1024 = true ∧ inB bs r 1024 = true ∧ inB bs h 1024 = true ∧
      sepB bs z 1024 h 1024 = true ∧ sepB bs r 1024 h 1024 = true ∧ z.1 ∈ bases ∧ z.2 < 2 ^ 31 ∧
      r.1 ∈ bases ∧ r.2 < 2 ^ 31 ∧ h.1 ∈ bases ∧ h.2 < 2 ^ 31 := by
  simp only [hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem hintArgs_ok {bs : List (Reg × Nat)} {z r h : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s) (hc : hintChk bs wbs z r h = true) :
    [Arg.ptr z, .ptr r, .imm γ, .ptr h].all Arg.ok = true := by
  obtain ⟨_, _, _, _, _, _, b1, o1, b2, o2, b3, o3⟩ := hintChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, b3, o3, decide_true, Bool.and_true,
    decide_eq_true (gamma2_lt hγ)]

theorem hintPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : hintChk (rbs ++ wbs) wbs z r h = true)
    (hA : ArgsIn [.ptr z, .ptr r, .imm γ, .ptr h] s s1) (rz : Reduced s.mem (pa s z))
    (rr : Reduced s.mem (pa s r)) :
    (makeHintContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s z), pR (pa s r)] [pR (pa s h)]) := by
  obtain ⟨_, i1, i2, i3, d13, d23, _⟩ := hintChk_spec hc
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  have hD : 8 ≤ D := by omega
  have hwf := ce_wfS (ws := [64, 64, 32, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s z), pR (pa s r)]
    [pR (pa s h)]
  sig_pre [makeHintContract, makeHintSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, Arg.val, sw32_ofNat (gamma2_lt hγ)]
  refine ⟨hwf, trivial, trivial, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_, A.L.nwp i1, A.L.nwp i2,
    A.L.nwp i3, hγ, A.red' i1 hD rz, A.red' i2 hD rr⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, conj_stk [pR (pa s z), pR (pa s r), pR (pa s h)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

theorem hintCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : hintChk (rbs ++ wbs) wbs z r h = true) (rz : Reduced s.mem (pa s z))
    (rr : Reduced s.mem (pa s r)) :
    WP isa (callP "vg_mldsa_make_hint" P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) s fun s' =>
      PPostB D s s' [(h, 1024)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      HintIs s'.mem (pa s h) 1 [Vector.zipWith (makeHint γ) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] ∧
      ((s'.gpr .rax).setWidth 32).toNat =
        hintOnes [Vector.zipWith (makeHint γ) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] := by
  obtain ⟨w1, i1, i2, i3, _⟩ := hintChk_spec hc
  have hD : 8 ≤ D := by have := hP.makeHint.hS; omega
  refine WP.mono (callP_ok hP.makeHint.ver.1 hP.makeHint.nosp hP.makeHint.depth L.dsm (hintArgs_ok hγ hc)
    (fun s1 hA hm k => hintPre hP.makeHint.hS (At.of L hm k) hγ hc hA rz rr)
    (covers_append (covers_cons (L.cR i1) (L.cR i2)) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [makeHintContract, makeHintSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, Arg.val, hm₂, er, A.poly' i1 hD, A.poly' i2 hD, sw32_ofNat (gamma2_lt hγ)] at hq
  exact hq

theorem hintCall_tr {P : Prims} (hP : PrimsOk P D) {z r h : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : hintChk (rbs ++ wbs) wbs z r h = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x z) ∧ Reduced x.mem (pa x r)) ∧
      (Reduced y.mem (pa y z) ∧ Reduced y.mem (pa y r)))
      (callP "vg_mldsa_make_hint" P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _⟩ := hintChk_spec hc
  refine callP_tr hP.makeHint.ver.1 hP.makeHint.ver.2.1 (hintArgs_ok hγ hc)
    fun x y x1 y1 ⟨R, ⟨rzx, rrx⟩, ⟨rzy, rry⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, hintPre hP.makeHint.hS (At.of R.lx hmx kx) hγ hc hAx rzx rrx,
        hintPre hP.makeHint.hS (At.of R.ly hmy ky) hγ hc hAy rzy rry, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_append (covers_cons (R.lx.cR i1) (R.lx.cR i2)) (covers_wr (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact covers_append (covers_cons (R.ly.cR i1) (R.ly.cR i2)) (covers_wr (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := argsIn4 hAy
  sig_pub [makeHintContract, makeHintSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign
