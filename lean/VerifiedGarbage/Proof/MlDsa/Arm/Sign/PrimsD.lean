import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsC

/-!
# ML-DSA signing on ARMv7: calls of the encodings with a stack argument

Untrusted: everything here is checked by Lean. As `Prims.lean`, for
`vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and `vg_mldsa_hint_bit_pack`,
whose fifth argument is on the stack (`callS`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem sp8 {s E : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hsp : E.sp = s.sp - BitVec.ofNat 32 8) :
    E.sp.toNat + 4 ≤ 2 ^ 32 := by
  have := L.sp; have := s.sp.isLt
  rw [hsp, sp_sub8 (by omega)]; omega

/-- The entry state of a stack call, as its preconditions below need it. -/
structure EntS (D : Nat) (rbs wbs : List (Reg × Nat)) (s : State) (S : Nat) (E : State) (v : BitVec 32) : Prop where
  en : Ent D rbs wbs s S E
  hS : S + 8 ≤ D
  sp : E.sp = s.sp - BitVec.ofNat 32 8
  aa : stackArgAddr E 0 = State.addr s.sp - BitVec.ofNat 64 8
  av : stackArg E 0 = v

theorem entS {s s1 : State} {S : Nat} (L : Lay D rbs wbs s) (k : Keep argRegs s s1) (hS : S + 8 ≤ D)
    (rd wr : List Region) :
    EntS D rbs wbs s S ((pushed [.r12, .lr] s1).callEntry.withRegions rd wr) (s1.gpr .r12) :=
  ⟨ent_S L k hS rd wr, hS, by rw [State.withRegions_sp, State.callEntry_sp, pushed_sp8, k.sp],
    (stk_arg L k (by omega) rd wr).1, (stk_arg L k (by omega) rd wr).2⟩

/-! ## `BitPack` -/

theorem bitPackParams_lt {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 32 * bitlen (a + b) < 2 ^ 32 ∧ 0 < 32 * bitlen (a + b) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- The coefficients of a polynomial of `R` in `[-a, b]`. -/
def InRange (m : Mem) (p : Addr) (a b : Nat) : Prop :=
  ∀ i < 256, -(a : Int) ≤ modPm (coeffAt m p i).toNat q ∧ modPm (coeffAt m p i).toNat q ≤ b

theorem bpArgs_ok {f out : Ptr} {a b len : Nat} (b1 : f.1 ∈ bases) (b2 : out.1 ∈ bases) :
    [Arg.ptr f, .imm a, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem bpPre {S len : Nat} {s E : State} (En : EntS D rbs wbs s S E (BitVec.ofNat 32 len)) {f out : Ptr} {a b : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 a)
    (g2 : E.gpr .r2 = BitVec.ofNat 32 b) (g3 : E.gpr .r3 = s.gpr out.1 + BitVec.ofNat 32 out.2)
    (hrd : E.rd = [pR (pa s f), argR s]) (hwr : E.wr = [⟨pa s out, len⟩])
    (hr : Reduced s.mem (pa s f)) (hrg : InRange s.mem (pa s f) a b) :
    (bitPackContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hD : 8 ≤ D := by have := En.hS; omega
  sig_pre [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.aa, En.av, En.en.L.w i1 (by decide), En.en.L.w i2 hl0, toNat32 ha', toNat32 hb',
    toNat32 hl']
  refine ⟨wf4 En.en.wf (sp8 En.en.L hD En.sp), hrd, hwr, En.en.L.disj d12, (argR_disj En.en.L hD i2).symm,
    conj_stk [pR (pa s f), ⟨pa s out, len⟩, argR s] ?_, En.en.L.fit i1 (by decide), En.en.L.fit i2 hl0, hp, hl,
    En.en.red i1 hr, fun i hi => by rw [En.en.coeff i1 hi]; exact hrg i hi⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨En.en.stk _ _ i1, En.en.stk _ _ i2, En.sp ▸ argR_stk En.en.L En.hS⟩

theorem bpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hr : Reduced s.mem (pa s f)) (hrg : InRange s.mem (pa s f) a b) :
    WP isa (bitPackAt P f a b out len) s fun s' => PPostB D s s' [(out, len)] ∧ CS s s' ∧
      bytesAt s'.mem (pa s out) len = bitPack ((polyAt s.mem (pa s f)).map fun c => modPm c.val q) a b := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hS := hP.bitPack.hS
  refine WP.mono (callS_ok hP.bitPack.ver.1 (by have := hP.bitPack.su; omega) (bpArgs_ok b1 b2) L.sp
    (rd := [pR (pa s f)]) (wr := [⟨pa s out, len⟩])
    (fun s1 hA k => by
      obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
      have En := entS (S := hP.bitPack.S) L k hS ([pR (pa s f)] ++ [argR s]) [⟨pa s out, len⟩]
      rw [e4] at En
      exact bpPre En hp hl hc (by rw [vS _ _ _ nl0, e0]; rfl) (by rw [vS _ _ _ nl1, e1]; rfl)
        (by rw [vS _ _ _ nl2, e2]; rfl) (by rw [vS _ _ _ nl3, e3]; rfl) rfl rfl hr hrg)
    (L.cR i1) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
  have En := ent_S (S := hP.bitPack.S) L k hS ([pR (pa s f)] ++ [argR s]) [⟨pa s out, len⟩]
  obtain ⟨-, av⟩ := stk_arg L k (by omega) ([pR (pa s f)] ++ [argR s]) [⟨pa s out, len⟩]
  set E := (pushed [.r12, .lr] s1).callEntry.withRegions ([pR (pa s f)] ++ [argR s]) [⟨pa s out, len⟩] with hE
  have g0 : E.gpr .r0 = s.gpr f.1 + BitVec.ofNat 32 f.2 := by rw [hE, vS _ _ _ nl0, e0]; rfl
  have g1 : E.gpr .r1 = BitVec.ofNat 32 a := by rw [hE, vS _ _ _ nl1, e1]; rfl
  have g2 : E.gpr .r2 = BitVec.ofNat 32 b := by rw [hE, vS _ _ _ nl2, e2]; rfl
  have g3 : E.gpr .r3 = s.gpr out.1 + BitVec.ofNat 32 out.2 := by rw [hE, vS _ _ _ nl3, e3]; rfl
  rw [e4] at av
  have ep := En.poly i1
  clear_value E
  sig_post [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [g0, g1, g2, g3, av, hm₂, toNat32 ha', toNat32 hb', toNat32 hl', L.w i1 (by decide), L.w i2 hl0,
    Arg.val, ep] at hq
  exact hq

theorem bpAt_tr {P : Prims} (hP : PrimsOk P D) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ InRange x.mem (pa x f) a b) ∧
      (Reduced y.mem (pa y f) ∧ InRange y.mem (pa y f) a b)) (bitPackAt P f a b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hS := hP.bitPack.hS
  have pre : ∀ {x x1 : State} (L : Lay D rbs wbs x) (k : Keep argRegs x x1)
      (hA : ArgsIn [.ptr f, .imm a, .imm b, .ptr out, .imm len] x x1) (hr : Reduced x.mem (pa x f))
      (hrg : InRange x.mem (pa x f) a b),
      (bitPackContract Arm.abi hP.bitPack.S).pre
        ((pushed [.r12, .lr] x1).callEntry.withRegions ([pR (pa x f)] ++ [argR x]) [⟨pa x out, len⟩]) := by
    intro x x1 L k hA hr hrg
    obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
    have En := entS (S := hP.bitPack.S) L k hS ([pR (pa x f)] ++ [argR x]) [⟨pa x out, len⟩]
    rw [e4] at En
    exact bpPre En hp hl hc (by rw [vS _ _ _ nl0, e0]; rfl) (by rw [vS _ _ _ nl1, e1]; rfl)
      (by rw [vS _ _ _ nl2, e2]; rfl) (by rw [vS _ _ _ nl3, e3]; rfl) rfl rfl hr hrg
  refine callS_tr hP.bitPack.ver.1 hP.bitPack.ver.2.1 (bpArgs_ok b1 b2) (fun x y h => h.1.sp)
    fun x y x1 y1 ⟨R, ⟨rx, gx⟩, ⟨ry, gy⟩⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, pre R.lx kx hAx rx gx, pre R.ly ky hAy ry gy, ?_,
      (cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).1, (cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).2,
      (cov_S R.ly ky (by omega) (R.ly.cR i1) (R.ly.cW w1)).1, (cov_S R.ly ky (by omega) (R.ly.cR i1) (R.ly.cW w1)).2⟩
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := argsIn5 hAx
  obtain ⟨hy0, hy1, hy2, hy3, hy4⟩ := argsIn5 hAy
  obtain ⟨-, vx⟩ := stk_arg R.lx kx (by omega) ([pR (pa x f)] ++ [argR x]) [⟨pa x out, len⟩]
  obtain ⟨-, vy⟩ := stk_arg R.ly ky (by omega) ([pR (pa y f)] ++ [argR y]) [⟨pa y out, len⟩]
  set X := (pushed [.r12, .lr] x1).callEntry.withRegions ([pR (pa x f)] ++ [argR x]) [⟨pa x out, len⟩] with hX
  set Y := (pushed [.r12, .lr] y1).callEntry.withRegions ([pR (pa y f)] ++ [argR y]) [⟨pa y out, len⟩] with hY
  have gx : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], X.gpr r = x1.gpr r := by
    intro r hr; rw [hX, vS _ _ _ (by revert hr; decide +revert)]
  have gy : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], Y.gpr r = y1.gpr r := by
    intro r hr; rw [hY, vS _ _ _ (by revert hr; decide +revert)]
  have sx : X.sp = x.sp - BitVec.ofNat 32 8 := by rw [hX, State.withRegions_sp, State.callEntry_sp, pushed_sp8, kx.sp]
  have sy : Y.sp = y.sp - BitVec.ofNat 32 8 := by rw [hY, State.withRegions_sp, State.callEntry_sp, pushed_sp8, ky.sp]
  clear_value X Y
  sig_pub [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [gx .r0 (by decide), gx .r1 (by decide), gx .r2 (by decide), gx .r3 (by decide),
    gy .r0 (by decide), gy .r1 (by decide), gy .r2 (by decide), gy .r3 (by decide), sx, sy,
    hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, vx, vy, hx4, hy4, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `BitUnpack` -/

theorem bupArgs_ok {v f : Ptr} {a b len : Nat} (b1 : v.1 ∈ bases) (b2 : f.1 ∈ bases) :
    [Arg.ptr v, .imm len, .imm a, .imm b, .ptr f].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem bupPre {S : Nat} {s E : State} {v f : Ptr} (En : EntS D rbs wbs s S E (s.gpr f.1 + BitVec.ofNat 32 f.2))
    {a b len : Nat} (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b))
    (hc : rwChk (rbs ++ wbs) wbs v len f 1024 = true)
    (g0 : E.gpr .r0 = s.gpr v.1 + BitVec.ofNat 32 v.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 len)
    (g2 : E.gpr .r2 = BitVec.ofNat 32 a) (g3 : E.gpr .r3 = BitVec.ofNat 32 b)
    (hrd : E.rd = [⟨pa s v, len⟩, argR s]) (hwr : E.wr = [pR (pa s f)]) :
    (bitUnpackContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hD : 8 ≤ D := by have := En.hS; omega
  sig_pre [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.aa, En.av, En.en.L.w i1 hl0, En.en.L.w i2 (by decide), toNat32 ha', toNat32 hb',
    toNat32 hl']
  refine ⟨wf4 En.en.wf (sp8 En.en.L hD En.sp), hrd, hwr, En.en.L.disj d12, (argR_disj En.en.L hD i2).symm,
    conj_stk [⟨pa s v, len⟩, pR (pa s f), argR s] ?_, En.en.L.fit i1 hl0, En.en.L.fit i2 (by decide), hp, hl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨En.en.stk _ _ i1, En.en.stk _ _ i2, En.sp ▸ argR_stk En.en.L En.hS⟩

theorem bupAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => PPostB D s s' [(f, 1024)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s f) (toRq (bitUnpack (bytesAt s.mem (pa s v) len) a b)) := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hS := hP.bitUnpack.hS
  refine WP.mono (callS_ok hP.bitUnpack.ver.1 (by have := hP.bitUnpack.su; omega) (bupArgs_ok b1 b2) L.sp
    (rd := [⟨pa s v, len⟩]) (wr := [pR (pa s f)])
    (fun s1 hA k => by
      obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
      have En := entS (S := hP.bitUnpack.S) L k hS ([⟨pa s v, len⟩] ++ [argR s]) [pR (pa s f)]
      rw [e4] at En
      exact bupPre En hp hl hc (by rw [vS _ _ _ nl0, e0]; rfl) (by rw [vS _ _ _ nl1, e1]; rfl)
        (by rw [vS _ _ _ nl2, e2]; rfl) (by rw [vS _ _ _ nl3, e3]; rfl) rfl rfl)
    (L.cR i1) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
  have En := ent_S (S := hP.bitUnpack.S) L k hS ([⟨pa s v, len⟩] ++ [argR s]) [pR (pa s f)]
  obtain ⟨-, av⟩ := stk_arg L k (by omega) ([⟨pa s v, len⟩] ++ [argR s]) [pR (pa s f)]
  set E := (pushed [.r12, .lr] s1).callEntry.withRegions ([⟨pa s v, len⟩] ++ [argR s]) [pR (pa s f)] with hE
  have g0 : E.gpr .r0 = s.gpr v.1 + BitVec.ofNat 32 v.2 := by rw [hE, vS _ _ _ nl0, e0]; rfl
  have g1 : E.gpr .r1 = BitVec.ofNat 32 len := by rw [hE, vS _ _ _ nl1, e1]; rfl
  have g2 : E.gpr .r2 = BitVec.ofNat 32 a := by rw [hE, vS _ _ _ nl2, e2]; rfl
  have g3 : E.gpr .r3 = BitVec.ofNat 32 b := by rw [hE, vS _ _ _ nl3, e3]; rfl
  rw [e4] at av
  have eb := En.bytes i1
  clear_value E
  sig_post [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [g0, g1, g2, g3, av, hm₂, toNat32 ha', toNat32 hb', toNat32 hl', L.w i1 hl0, L.w i2 (by decide),
    Arg.val, eb] at hq
  exact hq

theorem bupAt_tr {P : Prims} (hP : PrimsOk P D) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    RelCT isa (LRel D rbs wbs) (bitUnpackAt P v len a b f) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl', hl0⟩ := bitPackParams_lt hp
  rw [← hl] at hl' hl0
  have hS := hP.bitUnpack.hS
  have pre : ∀ {x x1 : State} (L : Lay D rbs wbs x) (k : Keep argRegs x x1)
      (hA : ArgsIn [.ptr v, .imm len, .imm a, .imm b, .ptr f] x x1),
      (bitUnpackContract Arm.abi hP.bitUnpack.S).pre
        ((pushed [.r12, .lr] x1).callEntry.withRegions ([⟨pa x v, len⟩] ++ [argR x]) [pR (pa x f)]) := by
    intro x x1 L k hA
    obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
    have En := entS (S := hP.bitUnpack.S) L k hS ([⟨pa x v, len⟩] ++ [argR x]) [pR (pa x f)]
    rw [e4] at En
    exact bupPre En hp hl hc (by rw [vS _ _ _ nl0, e0]; rfl) (by rw [vS _ _ _ nl1, e1]; rfl)
      (by rw [vS _ _ _ nl2, e2]; rfl) (by rw [vS _ _ _ nl3, e3]; rfl) rfl rfl
  refine callS_tr hP.bitUnpack.ver.1 hP.bitUnpack.ver.2.1 (bupArgs_ok b1 b2) (fun x y h => h.sp)
    fun x y x1 y1 R ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, pre R.lx kx hAx, pre R.ly ky hAy, ?_,
      (cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).1, (cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).2,
      (cov_S R.ly ky (by omega) (R.ly.cR i1) (R.ly.cW w1)).1, (cov_S R.ly ky (by omega) (R.ly.cR i1) (R.ly.cW w1)).2⟩
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := argsIn5 hAx
  obtain ⟨hy0, hy1, hy2, hy3, hy4⟩ := argsIn5 hAy
  obtain ⟨-, vx⟩ := stk_arg R.lx kx (by omega) ([⟨pa x v, len⟩] ++ [argR x]) [pR (pa x f)]
  obtain ⟨-, vy⟩ := stk_arg R.ly ky (by omega) ([⟨pa y v, len⟩] ++ [argR y]) [pR (pa y f)]
  set X := (pushed [.r12, .lr] x1).callEntry.withRegions ([⟨pa x v, len⟩] ++ [argR x]) [pR (pa x f)] with hX
  set Y := (pushed [.r12, .lr] y1).callEntry.withRegions ([⟨pa y v, len⟩] ++ [argR y]) [pR (pa y f)] with hY
  have gx : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], X.gpr r = x1.gpr r := by
    intro r hr; rw [hX, vS _ _ _ (by revert hr; decide +revert)]
  have gy : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], Y.gpr r = y1.gpr r := by
    intro r hr; rw [hY, vS _ _ _ (by revert hr; decide +revert)]
  have sx : X.sp = x.sp - BitVec.ofNat 32 8 := by rw [hX, State.withRegions_sp, State.callEntry_sp, pushed_sp8, kx.sp]
  have sy : Y.sp = y.sp - BitVec.ofNat 32 8 := by rw [hY, State.withRegions_sp, State.callEntry_sp, pushed_sp8, ky.sp]
  clear_value X Y
  sig_pub [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [gx .r0 (by decide), gx .r1 (by decide), gx .r2 (by decide), gx .r3 (by decide),
    gy .r0 (by decide), gy .r1 (by decide), gy .r2 (by decide), gy .r3 (by decide), sx, sy,
    hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, vx, vy, hx4, hy4, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `HintBitPack` -/

theorem hbpArgs_ok {h y : Ptr} {hlen ω len : Nat} (b1 : h.1 ∈ bases) (b2 : y.1 ∈ bases) :
    [Arg.ptr h, .imm hlen, .imm ω, .ptr y, .imm len].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem hintParams_lt {ω k : Nat} (h : (ω, k) ∈ hintParams) : ω < 2 ^ 32 ∧ ω + k < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hintParams_pos {ω k : Nat} (h : (ω, k) ∈ hintParams) : 0 < k := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hbpPre {S : Nat} {s E : State} {ω k : Nat} (En : EntS D rbs wbs s S E (BitVec.ofNat 32 (ω + k))) {h y : Ptr}
    (hp : (ω, k) ∈ hintParams) (hc : rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (g0 : E.gpr .r0 = s.gpr h.1 + BitVec.ofNat 32 h.2) (g1 : E.gpr .r1 = BitVec.ofNat 32 (256 * k))
    (g2 : E.gpr .r2 = BitVec.ofNat 32 ω) (g3 : E.gpr .r3 = s.gpr y.1 + BitVec.ofNat 32 y.2)
    (hrd : E.rd = [⟨pa s h, 256 * k * 4⟩, argR s]) (hwr : E.wr = [⟨pa s y, ω + k⟩])
    (hones : hintOnes (hintAt s.mem (pa s h) k) ≤ ω) :
    (hintBitPackContract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  have k0 := hintParams_pos hp
  have hD : 8 ≤ D := by have := En.hS; omega
  have ek : ω + k - ω = k := by omega
  have i1' : inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega]; exact i1
  sig_pre [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.aa, En.av, En.en.L.w i1 (by omega), En.en.L.w i2 (by omega), toNat32 h1,
    toNat32 h2, toNat32 h3, ek]
  refine ⟨wf4 En.en.wf (sp8 En.en.L hD En.sp), hrd, hwr, En.en.L.disj d12, (argR_disj En.en.L hD i2).symm,
    conj_stk [⟨pa s h, 256 * k * 4⟩, ⟨pa s y, ω + k⟩, argR s] ?_, En.en.L.fit i1 (by omega), En.en.L.fit i2 (by omega),
    hp, by omega, trivial, by rw [En.en.hint i1']; exact hones⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨En.en.stk _ _ i1, En.en.stk _ _ i2, En.sp ▸ argR_stk En.en.L En.hS⟩

theorem hbpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {h y : Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (hones : hintOnes (hintAt s.mem (pa s h) k) ≤ ω) :
    WP isa (hintBitPackAt P h (256 * k) ω y (ω + k)) s fun s' => PPostB D s s' [(y, ω + k)] ∧ CS s s' ∧
      bytesAt s'.mem (pa s y) (ω + k) = hintBitPack ω k (hintAt s.mem (pa s h) k) := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  have k0 := hintParams_pos hp
  have ek : ω + k - ω = k := by omega
  have i1' : inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega]; exact i1
  have hS := hP.hintBitPack.hS
  refine WP.mono (callS_ok hP.hintBitPack.ver.1 (by have := hP.hintBitPack.su; omega) (hbpArgs_ok b1 b2) L.sp
    (rd := [⟨pa s h, 256 * k * 4⟩]) (wr := [⟨pa s y, ω + k⟩])
    (fun s1 hA k' => by
      obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
      have En := entS (S := hP.hintBitPack.S) L k' hS ([⟨pa s h, 256 * k * 4⟩] ++ [argR s]) [⟨pa s y, ω + k⟩]
      rw [e4] at En
      exact hbpPre En hp hc (by rw [vS _ _ _ nl0, e0]; rfl) (by rw [vS _ _ _ nl1, e1]; rfl)
        (by rw [vS _ _ _ nl2, e2]; rfl) (by rw [vS _ _ _ nl3, e3]; rfl) rfl rfl hones)
    (L.cR i1) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k', s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
  have En := ent_S (S := hP.hintBitPack.S) L k' hS ([⟨pa s h, 256 * k * 4⟩] ++ [argR s]) [⟨pa s y, ω + k⟩]
  obtain ⟨-, av⟩ := stk_arg L k' (by omega) ([⟨pa s h, 256 * k * 4⟩] ++ [argR s]) [⟨pa s y, ω + k⟩]
  set E := (pushed [.r12, .lr] s1).callEntry.withRegions ([⟨pa s h, 256 * k * 4⟩] ++ [argR s]) [⟨pa s y, ω + k⟩]
    with hE
  have g0 : E.gpr .r0 = s.gpr h.1 + BitVec.ofNat 32 h.2 := by rw [hE, vS _ _ _ nl0, e0]; rfl
  have g2 : E.gpr .r2 = BitVec.ofNat 32 ω := by rw [hE, vS _ _ _ nl2, e2]; rfl
  have g3 : E.gpr .r3 = s.gpr y.1 + BitVec.ofNat 32 y.2 := by rw [hE, vS _ _ _ nl3, e3]; rfl
  rw [e4] at av
  have eh := En.hint i1'
  clear_value E
  sig_post [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [g0, g2, g3, av, hm₂, toNat32 h1, toNat32 h2, ek, L.w i1 (by omega), L.w i2 (by omega), Arg.val,
    eh] at hq
  exact hq

/-- Two runs leak the same when their hints (as the `u32`s at `h`) agree. -/
theorem hbpAt_tr {P : Prims} (hP : PrimsOk P D) {h y : Ptr} {ω k : Nat} (hp : (ω, k) ∈ hintParams)
    (hc : rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true) :
    RelCT isa (fun x z => LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (pa z h) i).toNat))
      (hintBitPackAt P h (256 * k) ω y (ω + k)) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  have k0 := hintParams_pos hp
  have hS := hP.hintBitPack.hS
  have pre : ∀ {x x1 : State} (L : Lay D rbs wbs x) (k' : Keep argRegs x x1)
      (hA : ArgsIn [.ptr h, .imm (256 * k), .imm ω, .ptr y, .imm (ω + k)] x x1)
      (hones : hintOnes (hintAt x.mem (pa x h) k) ≤ ω),
      (hintBitPackContract Arm.abi hP.hintBitPack.S).pre
        ((pushed [.r12, .lr] x1).callEntry.withRegions ([⟨pa x h, 256 * k * 4⟩] ++ [argR x]) [⟨pa x y, ω + k⟩]) := by
    intro x x1 L k' hA hones
    obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
    have En := entS (S := hP.hintBitPack.S) L k' hS ([⟨pa x h, 256 * k * 4⟩] ++ [argR x]) [⟨pa x y, ω + k⟩]
    rw [e4] at En
    exact hbpPre En hp hc (by rw [vS _ _ _ nl0, e0]; rfl) (by rw [vS _ _ _ nl1, e1]; rfl)
      (by rw [vS _ _ _ nl2, e2]; rfl) (by rw [vS _ _ _ nl3, e3]; rfl) rfl rfl hones
  refine callS_tr hP.hintBitPack.ver.1 hP.hintBitPack.ver.2.1 (hbpArgs_ok b1 b2) (fun x z h => h.1.sp)
    fun x z x1 z1 ⟨R, ox, oz, hl⟩ ⟨hAx, kx⟩ ⟨hAz, kz⟩ =>
    ⟨_, _, _, _, pre R.lx kx hAx ox, pre R.ly kz hAz oz, ?_,
      (cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).1, (cov_S R.lx kx (by omega) (R.lx.cR i1) (R.lx.cW w1)).2,
      (cov_S R.ly kz (by omega) (R.ly.cR i1) (R.ly.cW w1)).1, (cov_S R.ly kz (by omega) (R.ly.cR i1) (R.ly.cW w1)).2⟩
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := argsIn5 hAx
  obtain ⟨hz0, hz1, hz2, hz3, hz4⟩ := argsIn5 hAz
  have Ex := ent_S (S := hP.hintBitPack.S) R.lx kx hS ([⟨pa x h, 256 * k * 4⟩] ++ [argR x]) [⟨pa x y, ω + k⟩]
  have Ez := ent_S (S := hP.hintBitPack.S) R.ly kz hS ([⟨pa z h, 256 * k * 4⟩] ++ [argR z]) [⟨pa z y, ω + k⟩]
  obtain ⟨-, vx⟩ := stk_arg R.lx kx (by omega) ([⟨pa x h, 256 * k * 4⟩] ++ [argR x]) [⟨pa x y, ω + k⟩]
  obtain ⟨-, vz⟩ := stk_arg R.ly kz (by omega) ([⟨pa z h, 256 * k * 4⟩] ++ [argR z]) [⟨pa z y, ω + k⟩]
  set X := (pushed [.r12, .lr] x1).callEntry.withRegions ([⟨pa x h, 256 * k * 4⟩] ++ [argR x]) [⟨pa x y, ω + k⟩]
    with hX
  set Z := (pushed [.r12, .lr] z1).callEntry.withRegions ([⟨pa z h, 256 * k * 4⟩] ++ [argR z]) [⟨pa z y, ω + k⟩]
    with hZ
  have gx : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], X.gpr r = x1.gpr r := by
    intro r hr; rw [hX, vS _ _ _ (by revert hr; decide +revert)]
  have gz : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], Z.gpr r = z1.gpr r := by
    intro r hr; rw [hZ, vS _ _ _ (by revert hr; decide +revert)]
  have sx : X.sp = x.sp - BitVec.ofNat 32 8 := by rw [hX, State.withRegions_sp, State.callEntry_sp, pushed_sp8, kx.sp]
  have sz : Z.sp = z.sp - BitVec.ofNat 32 8 := by rw [hZ, State.withRegions_sp, State.callEntry_sp, pushed_sp8, kz.sp]
  have cx := Ex.coeffs (len := 256 * k) (p := h) (by rw [show 256 * k * 4 = 256 * k * 4 from rfl]; exact i1)
  have cz := Ez.coeffs (len := 256 * k) (p := h) i1
  clear_value X Z
  sig_pub [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [gx .r0 (by decide), gx .r1 (by decide), gx .r2 (by decide), gx .r3 (by decide),
    gz .r0 (by decide), gz .r1 (by decide), gz .r2 (by decide), gz .r3 (by decide), sx, sz,
    hx0, hx1, hx2, hx3, hz0, hz1, hz2, hz3, vx, vz, hx4, hz4, Arg.val, toNat32 h3]
  rw [R.lx.w i1 (by omega), R.ly.w i1 (by omega), cx, cz, hl]
  simp only [R.eq i1, R.eq i2, R.sp, and_self]

end

end VG.Proof.MlDsa.Arm.Sign
