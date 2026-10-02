import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Glue

/-!
# ML-DSA signing on x86-64: the primitives it calls

What the proofs need of the implementations of the primitives (`PrimsOk`):
each is verified against its shared contract (`Spec/MlDsa/Poly.lean`) for a
stack that fits in the `D` bytes the function gives its calls (`Callee`); and,
of the samplers whose result the function branches on, that the result is
public in their own runs (`RetPub`) and that they succeed only when the
algorithm finishes within `maxBounds`, the bounds the leakage of signing is
stated for.

For each call of an arithmetic primitive: what it does (`…At_ok`), and that
two runs in the same layout leak the same (`…At_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What the proofs need of the implementations `P` of the primitives, with
`D` bytes of stack for each call. -/
structure PrimsOk (P : Prims) (D : Nat) where
  ntt : Callee (fun S => nttContract X86_64.abi S) D P.ntt
  invNtt : Callee (fun S => nttInvContract X86_64.abi S) D P.invNtt
  mul : Callee (fun S => mulContract X86_64.abi S) D P.mul
  mulAdd : Callee (fun S => mulAddContract X86_64.abi S) D P.mulAdd
  add : Callee (fun S => addContract X86_64.abi S) D P.add
  sub : Callee (fun S => subContract X86_64.abi S) D P.sub
  rejNTT : Callee (fun S => rejNTTContract X86_64.abi S) D P.rejNTT
  expandMask : Callee (fun S => expandMaskContract X86_64.abi S) D P.expandMask
  ball : Callee (fun S => sampleInBallContract X86_64.abi S) D P.ball
  highBits : Callee (fun S => highBitsContract X86_64.abi S) D P.highBits
  lowBits : Callee (fun S => lowBitsContract X86_64.abi S) D P.lowBits
  normLt : Callee (fun S => normLtContract X86_64.abi S) D P.normLt
  makeHint : Callee (fun S => makeHintContract X86_64.abi S) D P.makeHint
  simpleBitPack : Callee (fun S => simpleBitPackContract X86_64.abi S) D P.simpleBitPack
  bitPack : Callee (fun S => bitPackContract X86_64.abi S) D P.bitPack
  bitUnpack : Callee (fun S => bitUnpackContract X86_64.abi S) D P.bitUnpack
  hintBitPack : Callee (fun S => hintBitPackContract X86_64.abi S) D P.hintBitPack
  rej4 : Callee (fun S => rejNTT4Contract X86_64.abi S) D P.rej4
  expandMask4 : Callee (fun S => expandMask4Contract X86_64.abi S) D P.expandMask4
  /-- `vg_mldsa_rej_ntt_poly`'s result depends only on its public data (its seed). -/
  rejRet : RetPub (rejNTTContract X86_64.abi rejNTT.S) P.rejNTT
  /-- `vg_mldsa_rej_ntt_poly` succeeds only if `RejNTTPoly` finishes within `maxBounds`. -/
  rejMax : ∀ s t s', (rejNTTContract X86_64.abi rejNTT.S).pre s → Exec isa P.rejNTT s t s' →
    (s'.gpr .rax).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (s.gpr .rdi) 34)).isSome
  /-- `vg_mldsa_rej_ntt_poly4`'s result depends only on its public data (its seeds). -/
  rej4Ret : RetPub (rejNTT4Contract X86_64.abi rej4.S) P.rej4
  /-- `vg_mldsa_rej_ntt_poly4` succeeds only if `RejNTTPoly` finishes within `maxBounds` on each seed. -/
  rej4Max : ∀ s t s', (rejNTT4Contract X86_64.abi rej4.S).pre s → Exec isa P.rej4 s t s' →
    (s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4, (rejNTTPoly maxBounds.rejNTT (seed4 s.mem (s.gpr .rdi) k)).isSome
  /-- `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`). -/
  ballRet : RetPub (sampleInBallContract X86_64.abi ball.S) P.ball
  /-- `vg_mldsa_sample_in_ball` succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballMax : ∀ s t s', (sampleInBallContract X86_64.abi ball.S).pre s → Exec isa P.ball s t s' →
    (s'.gpr .rax).setWidth 32 = 1 →
    (sampleInBall ((s.gpr .rdx).setWidth 32).toNat maxBounds.ball (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).isSome
  /-- `D` leaves room for the calls of the sponge functions. -/
  hD : 24 ≤ D
  hD' : D < 2 ^ 32

/-! ## The arguments of a call -/

theorem sw32_ofNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem toNat64 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; omega

theorem ptr_ok {p : Ptr} (h1 : p.1 ∈ bases) (h2 : p.2 < 2 ^ 31) : (Arg.ptr p).ok = true := by
  simp [Arg.ok, h1, h2]

theorem imm_ok {v : Nat} (h : v < 2 ^ 32) : (Arg.imm v).ok = true := by
  simp [Arg.ok, h]

/-- The setting of a call from a state in a layout: the stack pointer and
memory as they were, and the layout. -/
structure At (D : Nat) (rbs wbs : List (Reg × Nat)) (s s1 : State) : Prop where
  L : Lay D rbs wbs s
  mem : s1.mem = s.mem
  rsp : s1.gpr .rsp = s.gpr .rsp

theorem At.of {D : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (L : Lay D rbs wbs s) (hm : s1.mem = s.mem)
    (k : Keep argRegs s s1) : At D rbs wbs s s1 := ⟨L, hm, k.gpr (by decide)⟩

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (A : At D rbs wbs s s1)
include A

theorem At.ret {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) (hD : 8 ≤ D) :
    Region.Disjoint ⟨s1.gpr .rsp - 8, 8⟩ ⟨pa s p, l⟩ := by
  rw [A.rsp]; exact ce_ret (A.L.stkD h) hD A.L.dsm

theorem At.stk {S : Nat} (hS : S + 8 ≤ D) {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (below (s1.gpr .rsp - 8) S).Disjoint ⟨pa s p, l⟩ := by
  rw [A.rsp]; exact ce_below (A.L.stkD h) hS A.L.dsm

theorem At.k1 {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (below (s1.gpr .rsp) D).Disjoint ⟨pa s p, l⟩ := by
  rw [A.rsp]; exact A.L.stkD h

theorem At.poly {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    polyAt s1.callEntry.mem (pa s p) = polyAt s.mem (pa s p) := by
  rw [ce_polyAt s1 (A.k1 h) hD A.L.dsm, A.mem]

theorem At.natPoly {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    natPolyAt s1.callEntry.mem (pa s p) = natPolyAt s.mem (pa s p) := by
  rw [ce_natPolyAt s1 (A.k1 h) hD A.L.dsm, A.mem]

theorem At.red {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    Reduced s1.callEntry.mem (pa s p) ↔ Reduced s.mem (pa s p) := by
  rw [ce_reduced s1 (A.k1 h) hD A.L.dsm, A.mem]

theorem At.bytes {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) (hD : 8 ≤ D) :
    bytesAt s1.callEntry.mem (pa s p) l = bytesAt s.mem (pa s p) l := by
  rw [ce_bytesAt s1 (A.L.nwp h |> fun h' => by omega) (A.k1 h) hD A.L.dsm, A.mem]

theorem At.coeff {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) {i : Nat} (hi : i < 256) :
    coeffAt s1.callEntry.mem (pa s p) i = coeffAt s.mem (pa s p) i := by
  rw [coeffAt_congr₂ (p := pa s p) (m := s.mem) (fun k hk => ?_) hi]
  rw [← A.mem]; exact ce_byte s1 (R := pR (pa s p)) (A.k1 h) hD A.L.dsm (show 1024 ≤ 2 ^ 64 by decide) hk

theorem At.hint {p : Ptr} {k : Nat} (h : inB (rbs ++ wbs) p (1024 * k) = true) (hD : 8 ≤ D) :
    hintAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (pa s p) k = hintAt s.mem (pa s p) k := by
  rw [hintAt_congr (m := s.mem) fun x hx => ?_]
  rw [← A.mem]
  exact ce_byte s1 (R := ⟨pa s p, 1024 * k⟩) (A.k1 h) hD A.L.dsm (show 1024 * k ≤ 2 ^ 64 by have := A.L.nwp h; omega) hx

theorem At.coeffs {p : Ptr} {len : Nat} (h : inB (rbs ++ wbs) p (len * 4) = true) (hD : 8 ≤ D) :
    (List.range len).map (fun i => (coeffAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (pa s p) i).toNat) =
      (List.range len).map (fun i => (coeffAt s.mem (pa s p) i).toNat) := by
  rw [coeffs_congr (m := s.mem) fun x hx => ?_]
  rw [← A.mem]
  exact ce_byte s1 (R := ⟨pa s p, len * 4⟩) (A.k1 h) hD A.L.dsm (show len * 4 ≤ 2 ^ 64 by have := A.L.nwp h; omega)
    (show x < len * 4 by omega)

theorem At.coeff' {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) {i : Nat} (hi : i < 256) :
    coeffAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (pa s p) i = coeffAt s.mem (pa s p) i :=
  A.coeff h hD hi

theorem At.poly' {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    polyAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (pa s p) = polyAt s.mem (pa s p) :=
  A.poly h hD

theorem At.natPoly' {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) :
    natPolyAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (pa s p) = natPolyAt s.mem (pa s p) :=
  A.natPoly h hD

theorem At.bytes' {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) (hD : 8 ≤ D) :
    VG.Spec.Sha3.bytesAt (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (pa s p) l = bytesAt s.mem (pa s p) l :=
  A.bytes h hD

theorem At.red' {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (hD : 8 ≤ D) (hr : Reduced s.mem (pa s p)) :
    Reduced (s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)) (pa s p) :=
  (A.red h hD).mpr hr

end

/-! ## `NTT` and `NTT⁻¹` in place -/

section
variable {P : Prims} {D : Nat} {rbs wbs : List (Reg × Nat)}

/-- What a call of an in-place transformation of `f` needs of the layout. -/
def ipChk (bs wbs : List (Reg × Nat)) (f : Ptr) : Bool :=
  inB wbs f 1024 && inB wbs (sc oPS) 1024 && inB bs f 1024 && inB bs (sc oPS) 1024 &&
    sepB bs f 1024 (sc oPS) 1024 && decide (f.1 ∈ bases) && decide (f.2 < 2 ^ 31)

theorem ipChk_spec {bs wbs : List (Reg × Nat)} {f : Ptr} (h : ipChk bs wbs f = true) :
    inB wbs f 1024 = true ∧ inB wbs (sc oPS) 1024 = true ∧ inB bs f 1024 = true ∧ inB bs (sc oPS) 1024 = true ∧
      sepB bs f 1024 (sc oPS) 1024 = true ∧ f.1 ∈ bases ∧ f.2 < 2 ^ 31 := by
  simp only [ipChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem ipPre {t : Poly → Poly} {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {f : Ptr}
    (hc : ipChk (rbs ++ wbs) wbs f = true) (hA : ArgsIn [.ptr f, .ptr (sc oPS)] s s1)
    (hr : Reduced s.mem (pa s f)) :
    (inPlaceContract X86_64.abi t S).pre (s1.callEntry.withRegions [] [pR (pa s f), pR (pa s (sc oPS))]) := by
  obtain ⟨_, _, i1, i2, d12, _, _⟩ := ipChk_spec hc
  obtain ⟨h1, h2⟩ := argsIn2 hA
  have hD : 8 ≤ D := by omega
  have hwf := ce_wfS (ws := [64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [] [pR (pa s f), pR (pa s (sc oPS))]
  sig_pre [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [h1, h2, Arg.val]
  refine ⟨hwf, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, ?_⟩
  · refine Sig.conj_cons.mpr ⟨A.ret i2 hD, ?_⟩
    exact conj_stk [pR (pa s f), pR (pa s (sc oPS))] (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨A.stk hS i1, A.stk hS i2⟩)
  · exact (A.red i1 hD).mpr hr

theorem ipAt_ok {t : Poly → Poly} {n : String} {c : Prog isa} (C : Callee (fun S => inPlaceContract X86_64.abi t S) D c)
    {s : State} (L : Lay D rbs wbs s) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true)
    (hr : Reduced s.mem (pa s f)) :
    WP isa (callP n c [.ptr f, .ptr (sc oPS)]) s fun s' => PPostB D s s' [(f, 1024), (sc oPS, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f))) := by
  obtain ⟨w1, w2, i1, _, _, b1, o1⟩ := ipChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (callP_ok C.ver.1 C.nosp C.depth L.dsm (by simp [Arg.ok, b1, o1]; decide)
    (fun s1 hA hm k => ipPre C.hS (At.of L hm k) hc hA hr) (covers_wr (covers_cons (L.cW w1) (L.cW w2)))
    (covers_cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨h1, _⟩ := argsIn2 hA
  sig_post [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [h1, Arg.val, hm₂, ← State.callEntry_mem, A.poly i1 hD] at hq
  exact hq

theorem ipAt_tr {t : Poly → Poly} {n : String} {c : Prog isa} (C : Callee (fun S => inPlaceContract X86_64.abi t S) D c)
    {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f))
      (callP n c [.ptr f, .ptr (sc oPS)]) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, _, b1, o1⟩ := ipChk_spec hc
  refine callP_tr C.ver.1 C.ver.2.1 (by simp [Arg.ok, b1, o1]; decide)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, ipPre C.hS (At.of R.lx hmx kx) hc hAx rx, ipPre C.hS (At.of R.ly hmy ky) hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_wr (covers_cons (R.lx.cW w1) (R.lx.cW w2)),
        by rw [kx.2.2]; exact covers_cons (R.lx.cW w1) (R.lx.cW w2),
        by rw [ky.2.1, ky.2.2]; exact covers_wr (covers_cons (R.ly.cW w1) (R.ly.cW w2)),
        by rw [ky.2.2]; exact covers_cons (R.ly.cW w1) (R.ly.cW w2),
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2⟩ := argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := argsIn2 hAy
  sig_pub [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hy1, hy2, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## Products -/

/-- What a call of `vg_mldsa_multiply_ntt` or `vg_mldsa_multiply_add_ntt` on
`h`, `f`, `g` needs of the layout. -/
def mulChk (bs wbs : List (Reg × Nat)) (h f g : Ptr) : Bool :=
  inB wbs h 1024 && inB bs h 1024 && inB bs f 1024 && inB bs g 1024 && sepB bs h 1024 f 1024 &&
    sepB bs h 1024 g 1024 && decide (h.1 ∈ bases) && decide (h.2 < 2 ^ 31) && decide (f.1 ∈ bases) &&
    decide (f.2 < 2 ^ 31) && decide (g.1 ∈ bases) && decide (g.2 < 2 ^ 31)

theorem mulChk_spec {bs wbs : List (Reg × Nat)} {h f g : Ptr} (hc : mulChk bs wbs h f g = true) :
    inB wbs h 1024 = true ∧ inB bs h 1024 = true ∧ inB bs f 1024 = true ∧ inB bs g 1024 = true ∧
      sepB bs h 1024 f 1024 = true ∧ sepB bs h 1024 g 1024 = true ∧
      ([Arg.ptr h, .ptr f, .ptr g].all Arg.ok) = true := by
  simp only [mulChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, by simp [Arg.ok, h7, h8, h9, h10, h11, h12]⟩

theorem mulPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {h f g : Ptr}
    (hc : mulChk (rbs ++ wbs) wbs h f g = true) (hA : ArgsIn [.ptr h, .ptr f, .ptr g] s s1)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    (mulContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s f), pR (pa s g)] [pR (pa s h)]) := by
  obtain ⟨_, i1, i2, i3, d12, d13, _⟩ := mulChk_spec hc
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := ce_wfS (ws := [64, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s f), pR (pa s g)] [pR (pa s h)]
  sig_pre [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.ret i1 hD, A.ret i2 hD, ?_, A.L.nwp i1, A.L.nwp i2,
    A.L.nwp i3, A.red' i2 hD rf, A.red' i3 hD rg⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, conj_stk [pR (pa s h), pR (pa s f), pR (pa s g)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

theorem mulAddPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {h f g : Ptr}
    (hc : mulChk (rbs ++ wbs) wbs h f g = true) (hA : ArgsIn [.ptr h, .ptr f, .ptr g] s s1)
    (rh : Reduced s.mem (pa s h)) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    (mulAddContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s f), pR (pa s g)] [pR (pa s h)]) := by
  obtain ⟨_, i1, i2, i3, d12, d13, _⟩ := mulChk_spec hc
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  have hD : 8 ≤ D := by omega
  have hwf := ce_wfS (ws := [64, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s f), pR (pa s g)] [pR (pa s h)]
  sig_pre [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.L.disj d13, A.ret i1 hD, A.ret i2 hD, ?_, A.L.nwp i1, A.L.nwp i2,
    A.L.nwp i3, A.red' i1 hD rh, A.red' i2 hD rf, A.red' i3 hD rg⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, conj_stk [pR (pa s h), pR (pa s f), pR (pa s g)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

theorem mulAt_ok {P : Prims} (C : Callee (fun S => mulContract X86_64.abi S) D P.mul)
    {s : State} (L : Lay D rbs wbs s) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (mulAt P h f g) s fun s' => PPostB D s s' [(h, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (pa s h) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := mulChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (callP_ok C.ver.1 C.nosp C.depth L.dsm ok
    (fun s1 hA hm k => mulPre C.hS (At.of L hm k) hc hA rf rg)
    (covers_append (covers_cons (L.cR i2) (L.cR i3)) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  sig_post [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, A.poly' i2 hD, A.poly' i3 hD] at hq
  exact hq

theorem mulAddAt_ok {P : Prims} (C : Callee (fun S => mulAddContract X86_64.abi S) D P.mulAdd)
    {s : State} (L : Lay D rbs wbs s) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true)
    (rh : Reduced s.mem (pa s h)) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (mulAddAt P h f g) s fun s' => PPostB D s s' [(h, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (pa s h)
        (add (polyAt s.mem (pa s h)) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g)))) := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := mulChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega
  refine WP.mono (callP_ok C.ver.1 C.nosp C.depth L.dsm ok
    (fun s1 hA hm k => mulAddPre C.hS (At.of L hm k) hc hA rh rf rg)
    (covers_append (covers_cons (L.cR i2) (L.cR i3)) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  sig_post [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, A.poly' i1 hD, A.poly' i2 hD, A.poly' i3 hD] at hq
  exact hq

/-- Two runs in the same layout, with the arguments of a call in their registers. -/
theorem argsRel {D : Nat} {rbs wbs : List (Reg × Nat)} {x y x1 y1 : State} (R : LRel D rbs wbs x y)
    {as : List Arg} (hx : ArgsIn as x x1) (hy : ArgsIn as y y1)
    (hin : ∀ a ∈ as, match a with | .ptr p => ∃ l, inB (rbs ++ wbs) p l = true | .imm _ => True) :
    ∀ d ∈ argRegs6.zip as, x1.gpr d.1 = y1.gpr d.1 := by
  intro d hd
  rw [hx d hd, hy d hd]
  have := hin d.2 (List.of_mem_zip hd).2
  cases e : d.2 with
  | ptr p => rw [e] at this; obtain ⟨l, hl⟩ := this; simp only [Arg.val, R.pa hl]
  | imm v => rfl

theorem mulAt_tr {P : Prims} (C : Callee (fun S => mulContract X86_64.abi S) D P.mul)
    {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (mulAt P h f g) fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := mulChk_spec hc
  refine callP_tr C.ver.1 C.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rfx, rgx⟩, ⟨rfy, rgy⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, mulPre C.hS (At.of R.lx hmx kx) hc hAx rfx rgx, mulPre C.hS (At.of R.ly hmy ky) hc hAy rfy rgy, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_append (covers_cons (R.lx.cR i2) (R.lx.cR i3)) (covers_wr (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact covers_append (covers_cons (R.ly.cR i2) (R.ly.cR i3)) (covers_wr (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  sig_pub [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

theorem mulAddAt_tr {P : Prims} (C : Callee (fun S => mulAddContract X86_64.abi S) D P.mulAdd)
    {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧
      (Reduced x.mem (pa x h) ∧ Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y h) ∧ Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (mulAddAt P h f g)
      fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _, _, ok⟩ := mulChk_spec hc
  refine callP_tr C.ver.1 C.ver.2.1 ok
    fun x y x1 y1 ⟨R, ⟨rhx, rfx, rgx⟩, ⟨rhy, rfy, rgy⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, mulAddPre C.hS (At.of R.lx hmx kx) hc hAx rhx rfx rgx,
        mulAddPre C.hS (At.of R.ly hmy ky) hc hAy rhy rfy rgy, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_append (covers_cons (R.lx.cR i2) (R.lx.cR i3)) (covers_wr (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact covers_append (covers_cons (R.ly.cR i2) (R.ly.cR i3)) (covers_wr (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  sig_pub [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign
