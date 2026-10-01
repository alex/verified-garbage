import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Call
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# ML-DSA signing on ARMv7: the primitives it calls

Untrusted: everything here is checked by Lean. What the proofs need of the
implementations of the primitives (`PrimsOk`): each is verified against its
shared contract (`Spec/MlDsa/Poly.lean`) for a stack that, with the frame of
its stack arguments, fits in the `D` bytes the function gives its calls
(`Callee`); and, of the two samplers whose result the function branches on,
that the result is public in their own runs (`RetPub`) and that they
succeed only when the algorithm finishes within `maxBounds`, the bounds the
leakage of signing is stated for.

A callee's precondition is stated of its entry state `E` (`Ent`): its stack
pointer leaves `S` bytes below it, apart from the buffers of the layout, and
its memory agrees with the caller's on those buffers; the entry state of a
call with its arguments in registers is one (`ent_R`), and so is that of a
call with a frame of stack arguments (`ent_S`). For each call of an
arithmetic primitive: what it does (`…At_ok`), and that two runs in the
same layout leak the same (`…At_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (push2_frame push2_arg addr_sub setWidth_append32)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What the proofs need of the implementations `P` of the primitives, with
`D` bytes of stack for each call. -/
structure PrimsOk (P : Prims) (D : Nat) where
  ntt : Callee (fun S => nttContract Arm.abi S) 0 D P.ntt
  invNtt : Callee (fun S => nttInvContract Arm.abi S) 0 D P.invNtt
  mul : Callee (fun S => mulContract Arm.abi S) 0 D P.mul
  mulAdd : Callee (fun S => mulAddContract Arm.abi S) 0 D P.mulAdd
  add : Callee (fun S => addContract Arm.abi S) 0 D P.add
  sub : Callee (fun S => subContract Arm.abi S) 0 D P.sub
  rejNTT : Callee (fun S => rejNTTContract Arm.abi S) 0 D P.rejNTT
  expandMask : Callee (fun S => expandMaskContract Arm.abi S) 0 D P.expandMask
  ball : Callee (fun S => sampleInBallContract Arm.abi S) 8 D P.ball
  highBits : Callee (fun S => highBitsContract Arm.abi S) 0 D P.highBits
  lowBits : Callee (fun S => lowBitsContract Arm.abi S) 0 D P.lowBits
  normLt : Callee (fun S => normLtContract Arm.abi S) 0 D P.normLt
  makeHint : Callee (fun S => makeHintContract Arm.abi S) 0 D P.makeHint
  simpleBitPack : Callee (fun S => simpleBitPackContract Arm.abi S) 0 D P.simpleBitPack
  bitPack : Callee (fun S => bitPackContract Arm.abi S) 8 D P.bitPack
  bitUnpack : Callee (fun S => bitUnpackContract Arm.abi S) 8 D P.bitUnpack
  hintBitPack : Callee (fun S => hintBitPackContract Arm.abi S) 8 D P.hintBitPack
  /-- `vg_mldsa_rej_ntt_poly`'s result depends only on its public data (its seed). -/
  rejRet : RetPub (rejNTTContract Arm.abi rejNTT.S) P.rejNTT
  /-- `vg_mldsa_rej_ntt_poly` succeeds only if `RejNTTPoly` finishes within `maxBounds`. -/
  rejMax : ∀ s t s', (rejNTTContract Arm.abi rejNTT.S).pre s → Exec isa P.rejNTT s t s' →
    s'.gpr .r0 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (State.addr (s.gpr .r0)) 34)).isSome
  /-- `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`). -/
  ballRet : RetPub (sampleInBallContract Arm.abi ball.S) P.ball
  /-- `vg_mldsa_sample_in_ball` succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballMax : ∀ s t s', (sampleInBallContract Arm.abi ball.S).pre s → Exec isa P.ball s t s' →
    s'.gpr .r0 = 1 →
    (sampleInBall (s.gpr .r2).toNat maxBounds.ball (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)).isSome
  /-- `D` leaves room for the frames of the calls of the sponge functions. -/
  hD : 8 ≤ D
  hD' : D < 2 ^ 32

/-- `k` with the fact `X` of each run added to its postcondition. -/
def withPost (k : Contract isa) (X : State → State → Prop) : Contract isa :=
  { k with post := fun s s' => k.post s s' ∧ X s s' }

theorem hv_with {c : Prog isa} {k : Contract isa} {X : State → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hx : ∀ s t s', k.pre s → Exec isa c s t s' → X s s') :
    ∀ s, (withPost k X).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (withPost k X).post s s' :=
  fun s hs => let ⟨t, s', e, a, p⟩ := hv s hs; ⟨t, s', e, a, p, hx s t s' hs e⟩

/-! ## Values of arguments -/

theorem toNat32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; omega

/-! ## The entry state of a callee -/

/-- The entry state `E` of a callee called from `s` in a layout, for a
callee with a stack of `S` bytes: the `S` bytes below its stack pointer
lie apart from the buffers, and its memory agrees with `s`'s on them. -/
structure Ent (D : Nat) (rbs wbs : List (Reg × Nat)) (s : State) (S : Nat) (E : State) : Prop where
  L : Lay D rbs wbs s
  stk : ∀ p l, inB (rbs ++ wbs) p l = true → (belowA E.sp S).Disjoint ⟨pa s p, l⟩
  wf : S ≤ E.sp.toNat
  mem : ∀ p l, inB (rbs ++ wbs) p l = true → ∀ i < l, E.mem (pa s p + BitVec.ofNat 64 i) = s.mem (pa s p + BitVec.ofNat 64 i)

section
variable {D S : Nat} {rbs wbs : List (Reg × Nat)} {s E : State} (En : Ent D rbs wbs s S E)
include En

theorem Ent.poly {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) : polyAt E.mem (pa s p) = polyAt s.mem (pa s p) :=
  polyAt_congr fun k hk => En.mem p 1024 h k hk

theorem Ent.natPoly {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) :
    natPolyAt E.mem (pa s p) = natPolyAt s.mem (pa s p) :=
  natPolyAt_congr fun k hk => En.mem p 1024 h k hk

theorem Ent.red {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) (hr : Reduced s.mem (pa s p)) :
    Reduced E.mem (pa s p) :=
  reduced_congr (fun k hk => En.mem p 1024 h k hk) hr

theorem Ent.bytes {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    bytesAt E.mem (pa s p) l = bytesAt s.mem (pa s p) l :=
  VG.Proof.MlKem.bytesAt_congr fun k hk => En.mem p l h k hk

theorem Ent.coeff {p : Ptr} (h : inB (rbs ++ wbs) p 1024 = true) {i : Nat} (hi : i < 256) :
    coeffAt E.mem (pa s p) i = coeffAt s.mem (pa s p) i :=
  coeffAt_congr₂ (fun k hk => En.mem p 1024 h k hk) hi

theorem Ent.hint {p : Ptr} {k : Nat} (h : inB (rbs ++ wbs) p (1024 * k) = true) :
    hintAt E.mem (pa s p) k = hintAt s.mem (pa s p) k :=
  hintAt_congr fun x hx => En.mem p _ h x hx

theorem Ent.coeffs {p : Ptr} {len : Nat} (h : inB (rbs ++ wbs) p (len * 4) = true) :
    (List.range len).map (fun i => (coeffAt E.mem (pa s p) i).toNat) =
      (List.range len).map (fun i => (coeffAt s.mem (pa s p) i).toNat) :=
  coeffs_congr fun x hx => En.mem p _ h x (by omega)

/-- The stack of the callee, apart from buffers of the layout. -/
theorem Ent.conj {bs : List (Ptr × Nat)} (h : ∀ b ∈ bs, inB (rbs ++ wbs) b.1 b.2 = true) :
    Sig.conj ((List.map (fun r => (bs.map fun b => (⟨pa s b.1, b.2⟩ : Region)).map fun B => r.Disjoint B)
      (stackBelow (State.addr E.sp) S)).flatten) := by
  cases S with
  | zero => exact trivial
  | succ S =>
    simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [Sig.conj_map]
    intro B hB
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
    exact En.stk b.1 b.2 (h b hb)

end

/-- The stack of a callee, apart from the regions `bs`. -/
theorem conj_stk {sp : BitVec 32} {S : Nat} (bs : List Region) (h : ∀ B ∈ bs, (belowA sp S).Disjoint B) :
    Sig.conj ((List.map (fun r => bs.map fun B => r.Disjoint B) (stackBelow (State.addr sp) S)).flatten) := by
  cases S with
  | zero => exact trivial
  | succ S =>
    simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [Sig.conj_map]
    exact h

theorem wf0 {S : Nat} {sp : BitVec 32} (h : S ≤ sp.toNat) :
    (match (generalizing := false) S with | 0 => sp.toNat ≤ 2 ^ 32 | n => n ≤ sp.toNat ∧ sp.toNat ≤ 2 ^ 32) := by
  have := sp.isLt
  cases S <;> simp only <;> omega

theorem wf4 {S : Nat} {sp : BitVec 32} (h : S ≤ sp.toNat) (h' : sp.toNat + 4 ≤ 2 ^ 32) :
    (match (generalizing := false) S with
      | 0 => sp.toNat + 4 ≤ 2 ^ 32 | n => n ≤ sp.toNat ∧ sp.toNat + 4 ≤ 2 ^ 32) := by
  cases S <;> simp only <;> omega

/-- The entry state of a call with its arguments in registers. -/
theorem ent_R {D S : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (L : Lay D rbs wbs s)
    (k : Keep argRegs s s1) (hS : S ≤ D) (rd wr : List Region) :
    Ent D rbs wbs s S (s1.callEntry.withRegions rd wr) := by
  refine ⟨L, fun p l h => ?_, ?_, fun p l h i hi => ?_⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, k.sp]
    exact (L.stkD h).sub_left (belowA_sub hS)
  · simp only [State.withRegions_sp, State.callEntry_sp, k.sp]; have := L.sp; omega
  · simp only [State.withRegions_mem, State.callEntry_mem, k.mem]

theorem pushed_sp8 (s : State) : (pushed [.r12, .lr] s).sp = s.sp - BitVec.ofNat 32 8 := rfl

/-- The entry state of a call with a frame of stack arguments. -/
theorem ent_S {D S : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (L : Lay D rbs wbs s)
    (k : Keep argRegs s s1) (hS : S + 8 ≤ D) (rd wr : List Region) :
    Ent D rbs wbs s S ((pushed [.r12, .lr] s1).callEntry.withRegions rd wr) := by
  have h8 : 8 ≤ s.sp.toNat := by have := L.sp; omega
  refine ⟨L, fun p l h => ?_, ?_, fun p l h i hi => ?_⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp8, k.sp]
    exact (L.stkD h).sub_left fun x hx => belowA_sub (show 8 + S ≤ D by omega) x
      (belowA_push (by have := L.sp; omega) x hx)
  · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp8, k.sp, sp_sub8 h8]; have := L.sp; omega
  · simp only [State.withRegions_mem, State.callEntry_mem]
    have f := push2_frame (s := s1) (by rw [k.sp]; exact h8)
    rw [k.mem] at f
    refine f _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hd := (L.stkD h).sub_left (belowA_sub (show 8 ≤ D by omega))
    intro hc
    refine hd _ (by rw [← k.sp]; exact hc) (Offset.contains_base _ (by omega) (by have := L.nwp h; omega))

/-! ## The stack argument of a call with a frame -/

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s s1 : State} (L : Lay D rbs wbs s) (k : Keep argRegs s s1)
include L k

/-- The address and value of the stack argument, in the callee's entry state. -/
theorem stk_arg (hD : 8 ≤ D) (rd wr : List Region) :
    stackArgAddr ((pushed [.r12, .lr] s1).callEntry.withRegions rd wr) 0 = State.addr s.sp - BitVec.ofNat 64 8 ∧
      stackArg ((pushed [.r12, .lr] s1).callEntry.withRegions rd wr) 0 = s1.gpr .r12 := by
  have h8 : 8 ≤ s1.sp.toNat := by rw [k.sp]; have := L.sp; omega
  obtain ⟨a0, a1, -⟩ := push2_arg (t := (pushed [.r12, .lr] s1).callEntry.withRegions rd wr) h8 rfl rfl
  rw [← k.sp]; exact ⟨a0, a1⟩

/-- The regions a callee with a frame of stack arguments is given, in the
state after the push. -/
theorem cov_S (hD : 8 ≤ D) {rd wr : List Region} (hc : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers ((rd ++ [argR s]) ++ wr) ((pushed [.r12, .lr] s1).rd ++ (pushed [.r12, .lr] s1).wr) ∧
      Covers wr (pushed [.r12, .lr] s1).wr := by
  have h8 : 8 ≤ s1.sp.toNat := by rw [k.sp]; have := L.sp; omega
  have hwp : (pushed [.r12, .lr] s1).wr = belowA s.sp 8 :: s.wr := by
    rw [VG.Arm.pushed_wr, frame8 h8, k.wr, k.sp]
  rw [VG.Arm.pushed_rd, hwp, k.rd]
  refine ⟨fun x m hx => ?_, fun x m hx => ?_⟩
  · rcases (by simpa only [InRegions, List.mem_append, or_assoc] using hx : ∃ r, (r ∈ rd ∨ r ∈ [argR s] ∨ r ∈ wr) ∧
      r.Contains x m) with ⟨r, (hr | hr | hr), hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hc x m ⟨r, hr, hcr⟩
      rcases List.mem_append.mp hr' with h | h
      · exact ⟨r', List.mem_append_left _ h, hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h), hc'⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), argR_contains hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hw x m ⟨r, hr, hcr⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · obtain ⟨r', hr', hc'⟩ := hw x m hx
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

omit k in
/-- The stack argument lies apart from the buffers. -/
theorem argR_disj (hD : 8 ≤ D) {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (argR s).Disjoint ⟨pa s p, l⟩ :=
  (L.stkD h).sub_left fun x hx => belowA_sub hD x (argR_sub s x hx)

omit k in
/-- The stack argument lies above the callee's stack. -/
theorem argR_stk {S : Nat} (hS : S + 8 ≤ D) : (belowA (s.sp - BitVec.ofNat 32 8) S).Disjoint (argR s) := by
  have h8 : 8 ≤ s.sp.toNat := by have := L.sp; omega
  have := L.sp; have := s.sp.isLt
  simp only [belowA, argR]
  rw [addr_sub h8]
  exact (Offset.base_disjoint_below _ (by omega)).symm

end

/-! ## Registers of the entry state -/

theorem vR (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem vS (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, VG.Arm.pushed_gpr]

theorem nl0 : Reg.r0 ∉ linkRegs := by decide
theorem nl1 : Reg.r1 ∉ linkRegs := by decide
theorem nl2 : Reg.r2 ∉ linkRegs := by decide
theorem nl3 : Reg.r3 ∉ linkRegs := by decide

/-- The memory of the entry state of a call with its arguments in registers. -/
theorem vR_mem {s s1 : State} (k : Keep argRegs s s1) (rd wr : List Region) :
    (s1.callEntry.withRegions rd wr).mem = s.mem := by
  rw [State.withRegions_mem, State.callEntry_mem, k.mem]

/-! ## Addition and subtraction -/

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-- The contract of `vg_mldsa_add` (`t = add`) or `vg_mldsa_sub` (`t = sub`). -/
abbrev accC (t : Poly → Poly → Poly) (S : Nat) : Contract isa :=
  accSig.contract Arm.abi
    (pre := fun f g m => Reduced m f ∧ Reduced m g)
    (post := fun f g m m' _ => PolyIs m' f (t (polyAt m f) (polyAt m g)))
    (writeArgs := true)
    (stack := S)

/-- What a call of `vg_mldsa_add` or `vg_mldsa_sub` on `f`, `g` needs of the layout. -/
def accChk (bs wbs : List (Reg × Nat)) (f g : Ptr) : Bool :=
  inB wbs f 1024 && inB bs f 1024 && inB bs g 1024 && sepB bs f 1024 g 1024 && decide (f.1 ∈ bases) &&
    decide (g.1 ∈ bases)

theorem accChk_spec {bs wbs : List (Reg × Nat)} {f g : Ptr} (hc : accChk bs wbs f g = true) :
    inB wbs f 1024 = true ∧ inB bs f 1024 = true ∧ inB bs g 1024 = true ∧ sepB bs f 1024 g 1024 = true ∧
      ([Arg.ptr f, .ptr g].all Arg.ok) = true := by
  simp only [accChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, by simp [Arg.ok, h5, h6]⟩

theorem accPre {t : Poly → Poly → Poly} {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {f g : Ptr}
    (hc : accChk (rbs ++ wbs) wbs f g = true) (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2)
    (g1 : E.gpr .r1 = s.gpr g.1 + BitVec.ofNat 32 g.2) (hrd : E.rd = [pR (pa s g)]) (hwr : E.wr = [pR (pa s f)])
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    (accC t S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := accChk_spec hc
  sig_pre [accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, En.L.w i1 (by decide), En.L.w i2 (by decide)]
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.conj (bs := [(f, 1024), (g, 1024)]) (by simp [i1, i2]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide), En.red i1 rf, En.red i2 rg⟩

theorem accAt_ok {t : Poly → Poly → Poly} {n : String} {c : Prog isa} (C : Callee (fun S => accC t S) 0 D c)
    {s : State} (L : Lay D rbs wbs s) {f g : Ptr} (hc : accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (callR n c [.ptr f, .ptr g]) s fun s' => PPostB D s s' [(f, 1024)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  obtain ⟨w1, i1, i2, _, ok⟩ := accChk_spec hc
  refine WP.mono (callR_ok C.ver.1 (by have := C.su; have := C.hS; omega) ok L.sp
    (rd := [pR (pa s g)]) (wr := [pR (pa s f)])
    (fun s1 hA k => accPre (ent_R L k (by have := C.hS; omega) _ _) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn2 hA).2) rfl rfl rf rg)
    (covers_append (L.cR i2) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2⟩ := argsIn2 hA
  sig_post [accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, Arg.val, k.mem, L.w i1 (by decide), L.w i2 (by decide)] at hq
  exact hq

theorem accAt_tr {t : Poly → Poly → Poly} {n : String} {c : Prog isa} (C : Callee (fun S => accC t S) 0 D c)
    {f g : Ptr} (hc : accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (callR n c [.ptr f, .ptr g]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, ok⟩ := accChk_spec hc
  have hS : C.S ≤ D := by have := C.hS; omega
  refine callR_tr C.ver.1 C.ver.2.1 ok fun x y x1 y1 ⟨R, ⟨rfx, rgx⟩, ⟨rfy, rgy⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, accPre (ent_R R.lx kx hS [pR (pa x g)] [pR (pa x f)]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn2 hAx).2) rfl rfl rfx rgx,
      accPre (ent_R R.ly ky hS [pR (pa y g)] [pR (pa y f)]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn2 hAy).2) rfl rfl rfy rgy, ?_,
      by rw [kx.rd, kx.wr]; exact covers_append (R.lx.cR i2) (covers_wr (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact covers_append (R.ly.cR i2) (covers_wr (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2⟩ := argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := argsIn2 hAy
  sig_pub [accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hy1, hy2, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

theorem addAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f g : Ptr}
    (hc : accChk (rbs ++ wbs) wbs f g = true) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (addAt P f g) s fun s' => PPostB D s s' [(f, 1024)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s f) (add (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  accAt_ok (t := add) hP.add L hc rf rg

theorem subAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f g : Ptr}
    (hc : accChk (rbs ++ wbs) wbs f g = true) (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (subAt P f g) s fun s' => PPostB D s s' [(f, 1024)] ∧ CS s s' ∧
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

end

end VG.Proof.MlDsa.Arm.Sign
