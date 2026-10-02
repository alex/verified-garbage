import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inv

/-!
# ML-DSA signing on AArch64: the primitives it calls

What the proofs need of the implementations of the primitives (`PrimsOk`):
each is correct and constant time under its shared contract
(`Spec/MlDsa/Poly.lean`) with the `S` bytes of stack the function gives its
calls, and its frames use at most those (`CalleeOk`); and, of the two samplers
whose result the function branches on, that the result is public in their own
runs (`RetPub`) and that they succeed only when the algorithm finishes within
`maxBounds`, the bounds the leakage of signing is stated for.

For each call of a primitive, as the proof of signing uses it: what it does
(`…_ok`), and that two runs in the same layout leak the same (`…_tr`), from
the calls of `CallArith.lean` to `CallMore.lean`.
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What the proofs need of the implementations `P` of the primitives, with
`S` bytes of stack for each call. -/
structure PrimsOk (P : Prims) (S : Nat) : Prop where
  s16 : 16 ≤ S
  sl : S < 2 ^ 16
  ntt : CalleeOk S P.ntt (nttContract AArch64.abi S)
  invNtt : CalleeOk S P.invNtt (nttInvContract AArch64.abi S)
  mul : CalleeOk S P.mul (mulContract AArch64.abi S)
  mulAdd : CalleeOk S P.mulAdd (mulAddContract AArch64.abi S)
  add : CalleeOk S P.add (addContract AArch64.abi S)
  sub : CalleeOk S P.sub (subContract AArch64.abi S)
  rejNTT : CalleeOk S P.rejNTT (rejNTTContract AArch64.abi S)
  expandMask : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S)
  ball : CalleeOk S P.ball (sampleInBallContract AArch64.abi S)
  highBits : CalleeOk S P.highBits (highBitsContract AArch64.abi S)
  lowBits : CalleeOk S P.lowBits (lowBitsContract AArch64.abi S)
  normLt : CalleeOk S P.normLt (normLtContract AArch64.abi S)
  makeHint : CalleeOk S P.makeHint (makeHintContract AArch64.abi S)
  simpleBitPack : CalleeOk S P.simpleBitPack (simpleBitPackContract AArch64.abi S)
  bitPack : CalleeOk S P.bitPack (bitPackContract AArch64.abi S)
  bitUnpack : CalleeOk S P.bitUnpack (bitUnpackContract AArch64.abi S)
  hintBitPack : CalleeOk S P.hintBitPack (hintBitPackContract AArch64.abi S)
  /-- `vg_mldsa_rej_ntt_poly`'s result depends only on its public data (its seed). -/
  rejRet : RetPub (rejNTTContract AArch64.abi S) P.rejNTT
  /-- `vg_mldsa_rej_ntt_poly` succeeds only if `RejNTTPoly` finishes within `maxBounds`. -/
  rejMax : ∀ s t s', (rejNTTContract AArch64.abi S).pre s → Exec isa P.rejNTT s t s' →
    (s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (s.gpr .x0) 34)).isSome
  /-- `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`). -/
  ballRet : RetPub (sampleInBallContract AArch64.abi S) P.ball
  /-- `vg_mldsa_sample_in_ball` succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballMax : ∀ s t s', (sampleInBallContract AArch64.abi S).pre s → Exec isa P.ball s t s' →
    (s'.gpr .x0).setWidth 32 = 1 →
    (sampleInBall ((s.gpr .x2).setWidth 32).toNat maxBounds.ball (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).isSome

theorem PrimsOk.s64 {P : Prims} {S : Nat} (h : PrimsOk P S) : S < 2 ^ 64 := by have := h.sl; omega

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem LRel.same {x y : State} (R : LRel D rbs wbs x y) : SameB x y := ⟨R.regs, R.sp⟩

/-! ## `NTT` and `NTT⁻¹` in place -/

/-- What a call of an in-place transformation of `f` needs of the layout. -/
abbrev ipChkS (rbs wbs : List (Reg × Nat)) (f : Ptr) : Bool := ipChk rbs wbs f (sc oPS)

theorem ipAt_ok {t : Poly → Poly} {n : String} {c : Prog isa} (C : CalleeOk D c (inPlaceContract AArch64.abi t D))
    {s : State} (L : Lay D rbs wbs s) {f : Ptr} (hc : ipChkS rbs wbs f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (callAt n c [(.x0, .ptr f), (.x1, .ptr (sc oPS))]) s fun s' =>
      PPostB D s s' [(f, 1024), (sc oPS, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f))) :=
  AArch64.ipAt_ok L.s64 C L hc hr

theorem ipAt_tr {t : Poly → Poly} {n : String} {c : Prog isa} (C : CalleeOk D c (inPlaceContract AArch64.abi t D))
    {f : Ptr} (hc : ipChkS rbs wbs f = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f))
      (callAt n c [(.x0, .ptr f), (.x1, .ptr (sc oPS))]) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => AArch64.ipAt_tr (Q := fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f)) C hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## Products -/

theorem mulAt_ok {P : Prims} (C : CalleeOk D P.mul (mulContract AArch64.abi D))
    {s : State} (L : Lay D rbs wbs s) {h f g : Ptr} (hc : mulChk rbs wbs h f g = true)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (mulAt P h f g) s fun s' => PPostB D s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s h) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  AArch64.mulAt_ok L.s64 C L hc rf rg

theorem mulAddAt_ok {P : Prims} (C : CalleeOk D P.mulAdd (mulAddContract AArch64.abi D))
    {s : State} (L : Lay D rbs wbs s) {h f g : Ptr} (hc : mulChk rbs wbs h f g = true)
    (rh : Reduced s.mem (pa s h)) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (mulAddAt P h f g) s fun s' => PPostB D s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s h)
        (add (polyAt s.mem (pa s h)) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g)))) :=
  AArch64.mulAddAt_ok L.s64 C L hc rh rf rg

theorem mulAt_tr {P : Prims} (C : CalleeOk D P.mul (mulContract AArch64.abi D))
    {h f g : Ptr} (hc : mulChk rbs wbs h f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (mulAt P h f g) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => AArch64.mulAt_tr (Q := fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) C hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

theorem mulAddAt_tr {P : Prims} (C : CalleeOk D P.mulAdd (mulAddContract AArch64.abi D))
    {h f g : Ptr} (hc : mulChk rbs wbs h f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧
      (Reduced x.mem (pa x h) ∧ Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y h) ∧ Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (mulAddAt P h f g)
      fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => AArch64.mulAddAt_tr (Q := fun x y => LRel D rbs wbs x y ∧
      (Reduced x.mem (pa x h) ∧ Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y h) ∧ Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) C hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## Addition and subtraction -/

theorem addAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f g : Ptr}
    (hc : accChk rbs wbs f g = true) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (addAt P f g) s fun s' => PPostB D s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s f) (add (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  accAt_ok (op := add) L.s64 hP.add L hc rf rg

theorem subAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f g : Ptr}
    (hc : accChk rbs wbs f g = true) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (subAt P f g) s fun s' => PPostB D s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s f) (sub (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  accAt_ok (op := sub) L.s64 hP.sub L hc rf rg

theorem addAt_tr {P : Prims} (hP : PrimsOk P D) {f g : Ptr} (hc : accChk rbs wbs f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (addAt P f g) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => accAt_tr (Q := fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (op := add) hP.add hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

theorem subAt_tr {P : Prims} (hP : PrimsOk P D) {f g : Ptr} (hc : accChk rbs wbs f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (subAt P f g) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => accAt_tr (Q := fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (op := sub) hP.sub hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## `RejNTTPoly` -/

/-- What a call of `vg_mldsa_rej_ntt_poly` to `a` needs of the layout. -/
abbrev rejChkS (rbs wbs : List (Reg × Nat)) (a : Ptr) : Bool := rejNttChk rbs wbs (sc oRS) a (sc oPS)

/-- The call of `vg_mldsa_rej_ntt_poly`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds`. -/
theorem rejCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {a : Ptr}
    (hc : rejChkS rbs wbs a = true) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr a), (.x2, .ptr (sc oPS))]) s
      fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)) ((s'.gpr .x0).setWidth 32)
        (polyAt s'.mem (pa s a)) ∧
      ((s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)).isSome) := by
  have hc' := hc
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok L.s64 (hP.rejNTT.withPost hP.rejMax) (rejNtt_args L.ok c4 c5 c6)
    (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => rejNtt_pre L hc h1) (rejNtt_cov L hc).1
    (rejNtt_cov L hc).2) fun s' ⟨hP', s1, h1, hq, hx⟩ => ⟨hP'.b, hP'.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), Args.r0 h1, Args.mem h1, Arg.val] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem rejCall_tr {P : Prims} (hP : PrimsOk P D) {a : Ptr} (hc : rejChkS rbs wbs a = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34)
      (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr a), (.x2, .ptr (sc oPS))])
      fun x y => (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32 :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => rejNttAtK_trRet (Q := fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34) hP.rejNTT hP.rejRet hp.1.ok hc
    (fun _ _ ⟨R, hb⟩ => ⟨R.lx, R.ly, hb, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## `ExpandMask` -/

/-- What a call of `vg_mldsa_expand_mask_poly` to `a` needs of the layout. -/
abbrev maskChkS (rbs wbs : List (Reg × Nat)) (a : Ptr) : Bool := maskChk rbs wbs (sc oMS) a (sc oPS)

theorem maskAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : maskChkS rbs wbs a = true) :
    WP isa (maskAt P γ a) s fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s (sc oMS)) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) :=
  maskAtK_ok L.s64 hP.expandMask L hc hγ

theorem maskAt_tr {P : Prims} (hP : PrimsOk P D) {γ : Nat} {a : Ptr} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19)
    (hc : maskChkS rbs wbs a = true) :
    RelCT isa (LRel D rbs wbs) (maskAt P γ a) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => maskAtK_tr (Q := LRel D rbs wbs) hP.expandMask hp.ok hc hγ
    (fun _ _ R => ⟨R.lx, R.ly, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## `SampleInBall` -/

/-- What a call of `vg_mldsa_sample_in_ball` of the `len` bytes at `CT` to `c` needs of the layout. -/
abbrev ballChkS (rbs wbs : List (Reg × Nat)) (len : Nat) (c : Ptr) : Bool := ballChk rbs wbs (sc oCT) len c (sc oPS)

/-- The call of `vg_mldsa_sample_in_ball`: its outcome, and that it succeeds
only if `SampleInBall` finishes within `maxBounds`. -/
theorem ballCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : ballChkS rbs wbs len c = true) :
    WP isa (ballAt P len tau c) s fun s' =>
      PPostB D s s' [(c, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (pa s (sc oCT)) len)).map toRq)
        ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (pa s c)) ∧
      ((s'.gpr .x0).setWidth 32 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (pa s (sc oCT)) len)).isSome) := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok L.s64 (hP.ball.withPost hP.ballMax) (ball_args L.ok len tau c4 c5 c6)
    (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => ball_pre L hc hp h1) (ball_cov L hc).1
    (ball_cov L hc).2) fun s' ⟨hP', s1, h1, hq, hx⟩ => ⟨hP'.b, hP'.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), imm32 hl.2] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1,
    Arg.val] at hx
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), imm32 hl.2] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem ballCall_tr {P : Prims} (hP : PrimsOk P D) {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams)
    (hc : ballChkS rbs wbs len c = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oCT)) len = bytesAt y.mem (pa y (sc oCT)) len)
      (ballAt P len tau c) fun x y => (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32 :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => ballAtK_trRet (Q := fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oCT)) len = bytesAt y.mem (pa y (sc oCT)) len) hP.ball hP.ballRet hq.1.ok hc hp
    (fun _ _ ⟨R, hb⟩ => ⟨R.lx, R.ly, hb, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

/-! ## `HighBits` and `LowBits` -/

theorem highBitsAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk rbs wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (highBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      NatPolyIs s'.mem (pa s out) ((polyAt s.mem (pa s r)).map fun c => (highBits γ c).toNat) :=
  bitsAtK_ok (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) L.s64 hP.highBits L hc
    hγ hr

theorem highBitsAt_tr {P : Prims} (hP : PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk rbs wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (highBitsAt P r γ out) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ =>
    bitsAtK_tr (R := fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r)) (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) hP.highBits
      hq.1.ok hc hγ (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem lowBitsAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk rbs wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (lowBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s out) ((polyAt s.mem (pa s r)).map fun c => ofInt (lowBits γ c)) :=
  bitsAtK_ok (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (lowBits γ c))) L.s64 hP.lowBits L hc hγ hr

theorem lowBitsAt_tr {P : Prims} (hP : PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk rbs wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (lowBitsAt P r γ out) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ =>
    bitsAtK_tr (R := fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r)) (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (lowBits γ c))) hP.lowBits
      hq.1.ok hc hγ (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

/-! ## Norms -/

/-- What a call of `vg_mldsa_norm_lt` on `f` needs of the layout. -/
abbrev normChk (bs : List (Reg × Nat)) (f : Ptr) : Bool := inB bs f 1024

theorem normCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f : Ptr} {B : Nat}
    (hB : B < 2 ^ 32) (hc : normChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (callAt "vg_mldsa_norm_lt" P.normLt [(.x0, .ptr f), (.x1, .imm B)]) s fun s' => PPostB D s s' [] ∧
      s'.gpr .x24 = s.gpr .x24 ∧ (s'.gpr .x0).setWidth 32 = if normRq [polyAt s.mem (pa s f)] < B then 1 else 0 :=
  normAtK_ok L.s64 hP.normLt L hc hB hr

theorem normCall_tr {P : Prims} (hP : PrimsOk P D) {f : Ptr} {B : Nat} (hc : normChk (rbs ++ wbs) f = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f))
      (callAt "vg_mldsa_norm_lt" P.normLt [(.x0, .ptr f), (.x1, .imm B)]) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => normAtK_tr (Q := fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f)) hP.normLt hq.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

/-! ## `MakeHint` -/

theorem hintCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : hintChk rbs wbs z r h = true) (rz : Reduced s.mem (pa s z))
    (rr : Reduced s.mem (pa s r)) :
    WP isa (callAt "vg_mldsa_make_hint" P.makeHint [(.x0, .ptr z), (.x1, .ptr r), (.x2, .imm γ), (.x3, .ptr h)]) s
      fun s' => PPostB D s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      HintIs s'.mem (pa s h) 1 [Vector.zipWith (makeHint γ) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] ∧
      ((s'.gpr .x0).setWidth 32).toNat =
        hintOnes [Vector.zipWith (makeHint γ) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] :=
  hintAtK_ok L.s64 hP.makeHint L hc hγ rz rr

theorem hintCall_tr {P : Prims} (hP : PrimsOk P D) {z r h : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : hintChk rbs wbs z r h = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x z) ∧ Reduced x.mem (pa x r)) ∧
      (Reduced y.mem (pa y z) ∧ Reduced y.mem (pa y r)))
      (callAt "vg_mldsa_make_hint" P.makeHint [(.x0, .ptr z), (.x1, .ptr r), (.x2, .imm γ), (.x3, .ptr h)])
      fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => hintAtK_tr (Q := fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x z) ∧ Reduced x.mem (pa x r)) ∧
      (Reduced y.mem (pa y z) ∧ Reduced y.mem (pa y r))) hP.makeHint hq.1.ok hc hγ
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

/-! ## Encodings -/

theorem sbpOk_of {b len : Nat} (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) : SbpOk b len := by
  refine ⟨hb, hl, ?_⟩
  subst hl
  simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide

theorem sbpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk rbs wbs f 1024 out len = true)
    (hle : ∀ i < 256, (coeffAt s.mem (pa s f) i).toNat ≤ b) :
    WP isa (simpleBitPackAt P f b out len) s fun s' => PPostB D s s' [(out, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s out) len = simpleBitPack (natPolyAt s.mem (pa s f)) b :=
  sbpAtK_ok L.s64 hP.simpleBitPack L hc (sbpOk_of hb hl) hle

theorem sbpAt_tr {P : Prims} (hP : PrimsOk P D) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk rbs wbs f 1024 out len = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (∀ i < 256, (coeffAt x.mem (pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (coeffAt y.mem (pa y f) i).toNat ≤ b)) (simpleBitPackAt P f b out len) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => sbpAtK_tr (Q := fun x y => LRel D rbs wbs x y ∧ (∀ i < 256, (coeffAt x.mem (pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (coeffAt y.mem (pa y f) i).toNat ≤ b)) hP.simpleBitPack hq.1.ok hc (sbpOk_of hb hl)
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem bitPackParams_lt {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 32 * bitlen (a + b) < 2 ^ 32 := by
  simp only [bitPackParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bpOk_of {a b len : Nat} (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) : BpOk a b len := by
  obtain ⟨h1, h2, h3⟩ := bitPackParams_lt hp
  exact ⟨hp, hl, h1, h2, by rw [hl]; exact h3⟩

/-- The coefficients of a polynomial of `R` in `[-a, b]`. -/
abbrev InRange (m : Mem) (p : Addr) (a b : Nat) : Prop := BpRange m p a b

theorem bpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs f 1024 out len = true)
    (hr : Reduced s.mem (pa s f)) (hrg : InRange s.mem (pa s f) a b) :
    WP isa (bitPackAt P f a b out len) s fun s' => PPostB D s s' [(out, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s out) len = bitPack ((polyAt s.mem (pa s f)).map fun c => modPm c.val q) a b :=
  bpAtK_ok L.s64 hP.bitPack L hc (bpOk_of hp hl) hr hrg

theorem bpAt_tr {P : Prims} (hP : PrimsOk P D) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs f 1024 out len = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ InRange x.mem (pa x f) a b) ∧
      (Reduced y.mem (pa y f) ∧ InRange y.mem (pa y f) a b)) (bitPackAt P f a b out len) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => bpAtK_tr (Q := fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ InRange x.mem (pa x f) a b) ∧
      (Reduced y.mem (pa y f) ∧ InRange y.mem (pa y f) a b)) hP.bitPack hq.1.ok hc (bpOk_of hp hl)
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem bupAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs v len f 1024 = true) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => PPostB D s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s f) (toRq (bitUnpack (bytesAt s.mem (pa s v) len) a b)) :=
  buAtK_ok L.s64 hP.bitUnpack L hc (bpOk_of hp hl)

theorem bupAt_tr {P : Prims} (hP : PrimsOk P D) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs v len f 1024 = true) :
    RelCT isa (LRel D rbs wbs) (bitUnpackAt P v len a b f) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => buAtK_tr (Q := LRel D rbs wbs) hP.bitUnpack hq.ok hc (bpOk_of hp hl)
    (fun _ _ R => ⟨R.lx, R.ly, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem hintParams_lt {ω k : Nat} (h : (ω, k) ∈ hintParams) : ω < 2 ^ 32 ∧ ω + k < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hbpOk_of {ω k : Nat} (hp : (ω, k) ∈ hintParams) : HbpOk (256 * k) ω (ω + k) := by
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  exact ⟨by rw [show ω + k - ω = k by omega]; exact hp, by omega, by rw [show ω + k - ω = k by omega], h3, h1, h2⟩

theorem hbpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {h y : Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : rwChk rbs wbs h (256 * k * 4) y (ω + k) = true)
    (hones : hintOnes (hintAt s.mem (pa s h) k) ≤ ω) :
    WP isa (hintBitPackAt P h (256 * k) ω y (ω + k)) s fun s' => PPostB D s s' [(y, ω + k)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧ bytesAt s'.mem (pa s y) (ω + k) = hintBitPack ω k (hintAt s.mem (pa s h) k) := by
  have ek : ω + k - ω = k := by omega
  have := hbpAtK_ok L.s64 hP.hintBitPack L hc (hbpOk_of hp) (by rw [ek]; exact hones)
  rw [ek] at this
  exact this

/-- Two runs leak the same when their hints (as the `u32`s at `h`) agree. -/
theorem hbpAt_tr {P : Prims} (hP : PrimsOk P D) {h y : Ptr} {ω k : Nat} (hp : (ω, k) ∈ hintParams)
    (hc : rwChk rbs wbs h (256 * k * 4) y (ω + k) = true) :
    RelCT isa (fun x z => LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (pa z h) i).toNat))
      (hintBitPackAt P h (256 * k) ω y (ω + k)) fun _ _ => True := by
  have ek : ω + k - ω = k := by omega
  exact fun x z t₁ t₂ x' z' hq e₁ e₂ => hbpAtK_tr (Q := fun x z => LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (pa z h) i).toNat)) hP.hintBitPack hq.1.ok hc (hbpOk_of hp)
    (fun _ _ ⟨R, ox, oz, hl⟩ => ⟨R.lx, R.ly, by rw [ek]; exact ox, by rw [ek]; exact oz, hl, R.same⟩)
    x z t₁ t₂ x' z' hq e₁ e₂

end

end VG.Proof.MlDsa.AArch64.Sign
