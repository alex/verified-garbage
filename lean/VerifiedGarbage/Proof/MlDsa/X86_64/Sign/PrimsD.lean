import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PrimsC

/-!
# ML-DSA signing on x86-64: calls of the packing primitives

Untrusted: everything here is checked by Lean. As `Prims.lean`, for
`vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and
`vg_mldsa_hint_bit_pack` (which may leak the hint: two runs leak the same
when their hints agree, `hintPackAt_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## `SimpleBitPack` -/

theorem sbpArgs_ok {bs : List (Reg × Nat)} {f out : Ptr} {b len : Nat} (hb : b < 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : rwChk bs wbs f 1024 out len = true) : [Arg.ptr f, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true hb, decide_eq_true hl]

theorem sbpPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hA : ArgsIn [.ptr f, .imm b, .ptr out, .imm len] s s1)
    (hle : ∀ i < 256, (coeffAt s.mem (pa s f) i).toNat ≤ b) :
    (simpleBitPackContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s f)] [⟨pa s out, len⟩]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  have hD : 8 ≤ D := by omega
  have hb' : b < 2 ^ 32 ∧ len < 2 ^ 32 := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> decide
  have hwf := ce_wfS (ws := [64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s f)] [⟨pa s out, len⟩]
  sig_pre [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, Arg.val, sw32_ofNat hb'.1, toNat64 hb'.2]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hb, hl,
    fun i hi => by rw [A.coeff' i1 hD hi]; exact hle i hi⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [pR (pa s f), ⟨pa s out, len⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem sbpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hle : ∀ i < 256, (coeffAt s.mem (pa s f) i).toNat ≤ b) :
    WP isa (simpleBitPackAt P f b out len) s fun s' => PPostB D s s' [(out, len)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s out) len = simpleBitPack (natPolyAt s.mem (pa s f)) b := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.simpleBitPack.hS; omega
  have hb' : b < 2 ^ 32 ∧ len < 2 ^ 32 := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> decide
  refine WP.mono (callP_ok hP.simpleBitPack.ver.1 hP.simpleBitPack.nosp hP.simpleBitPack.depth L.dsm
    (sbpArgs_ok hb'.1 hb'.2 hc) (fun s1 hA hm k => sbpPre hP.simpleBitPack.hS (At.of L hm k) hb hl hc hA hle)
    (covers_append (L.cR i1) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  sig_post [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, Arg.val, hm₂, A.natPoly' i1 hD, sw32_ofNat hb'.1, toNat64 hb'.2] at hq
  exact hq

theorem sbpAt_tr {P : Prims} (hP : PrimsOk P D) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (∀ i < 256, (coeffAt x.mem (pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (coeffAt y.mem (pa y f) i).toNat ≤ b)) (simpleBitPackAt P f b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hb' : b < 2 ^ 32 ∧ len < 2 ^ 32 := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> decide
  refine callP_tr hP.simpleBitPack.ver.1 hP.simpleBitPack.ver.2.1 (sbpArgs_ok hb'.1 hb'.2 hc)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, sbpPre hP.simpleBitPack.hS (At.of R.lx hmx kx) hb hl hc hAx rx,
        sbpPre hP.simpleBitPack.hS (At.of R.ly hmy ky) hb hl hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_append (R.lx.cR i1) (covers_wr (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact covers_append (R.ly.cR i1) (covers_wr (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := argsIn4 hAy
  sig_pub [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `BitPack` -/

theorem bitPackParams_lt {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 32 * bitlen (a + b) < 2 ^ 32 := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bpArgs_ok {bs : List (Reg × Nat)} {f out : Ptr} {a b len : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : rwChk bs wbs f 1024 out len = true) : [Arg.ptr f, .imm a, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true ha, decide_eq_true hb, decide_eq_true hl]

/-- The coefficients of a polynomial of `R` in `[-a, b]`. -/
def InRange (m : Mem) (p : Addr) (a b : Nat) : Prop :=
  ∀ i < 256, -(a : Int) ≤ modPm (coeffAt m p i).toNat q ∧ modPm (coeffAt m p i).toNat q ≤ b

theorem bpPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hA : ArgsIn [.ptr f, .imm a, .imm b, .ptr out, .imm len] s s1) (hr : Reduced s.mem (pa s f))
    (hrg : InRange s.mem (pa s f) a b) :
    (bitPackContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s f)] [⟨pa s out, len⟩]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  have hD : 8 ≤ D := by omega
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  have hwf := ce_wfS (ws := [64, 32, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s f)] [⟨pa s out, len⟩]
  sig_pre [bitPackContract, bitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, sw32_ofNat ha', sw32_ofNat hb', toNat64 hl']
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hp, hl, A.red' i1 hD hr,
    fun i hi => by rw [A.coeff' i1 hD hi]; exact hrg i hi⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [pR (pa s f), ⟨pa s out, len⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem bpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hr : Reduced s.mem (pa s f)) (hrg : InRange s.mem (pa s f) a b) :
    WP isa (bitPackAt P f a b out len) s fun s' => PPostB D s s' [(out, len)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s out) len = bitPack ((polyAt s.mem (pa s f)).map fun c => modPm c.val q) a b := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.bitPack.hS; omega
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  refine WP.mono (callP_ok hP.bitPack.ver.1 hP.bitPack.nosp hP.bitPack.depth L.dsm (bpArgs_ok ha' hb' hl' hc)
    (fun s1 hA hm k => bpPre hP.bitPack.hS (At.of L hm k) hp hl hc hA hr hrg)
    (covers_append (L.cR i1) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  sig_post [bitPackContract, bitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, e5, Arg.val, hm₂, A.poly' i1 hD, sw32_ofNat ha', sw32_ofNat hb', toNat64 hl'] at hq
  exact hq

theorem bpAt_tr {P : Prims} (hP : PrimsOk P D) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ InRange x.mem (pa x f) a b) ∧
      (Reduced y.mem (pa y f) ∧ InRange y.mem (pa y f) a b)) (bitPackAt P f a b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  refine callP_tr hP.bitPack.ver.1 hP.bitPack.ver.2.1 (bpArgs_ok ha' hb' hl' hc)
    fun x y x1 y1 ⟨R, ⟨rx, gx⟩, ⟨ry, gy⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, bpPre hP.bitPack.hS (At.of R.lx hmx kx) hp hl hc hAx rx gx,
        bpPre hP.bitPack.hS (At.of R.ly hmy ky) hp hl hc hAy ry gy, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_append (R.lx.cR i1) (covers_wr (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact covers_append (R.ly.cR i1) (covers_wr (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := argsIn5 hAx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := argsIn5 hAy
  sig_pub [bitPackContract, bitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hy1, hy2, hy3, hy4, hy5, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `BitUnpack` -/

theorem bupArgs_ok {bs : List (Reg × Nat)} {v f : Ptr} {a b len : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : rwChk bs wbs v len f 1024 = true) : [Arg.ptr v, .imm len, .imm a, .imm b, .ptr f].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true ha, decide_eq_true hb, decide_eq_true hl]

theorem bupPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs v len f 1024 = true)
    (hA : ArgsIn [.ptr v, .imm len, .imm a, .imm b, .ptr f] s s1) :
    (bitUnpackContract X86_64.abi S).pre (s1.callEntry.withRegions [⟨pa s v, len⟩] [pR (pa s f)]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  have hD : 8 ≤ D := by omega
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  have hwf := ce_wfS (ws := [64, 64, 32, 32, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨pa s v, len⟩] [pR (pa s f)]
  sig_pre [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, sw32_ofNat ha', sw32_ofNat hb', toNat64 hl']
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hp, hl⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [⟨pa s v, len⟩, pR (pa s f)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem bupAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => PPostB D s s' [(f, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (pa s f) (toRq (bitUnpack (bytesAt s.mem (pa s v) len) a b)) := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.bitUnpack.hS; omega
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  refine WP.mono (callP_ok hP.bitUnpack.ver.1 hP.bitUnpack.nosp hP.bitUnpack.depth L.dsm (bupArgs_ok ha' hb' hl' hc)
    (fun s1 hA hm k => bupPre hP.bitUnpack.hS (At.of L hm k) hp hl hc hA)
    (covers_append (L.cR i1) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  sig_post [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, e5, Arg.val, hm₂, A.bytes' i1 hD, sw32_ofNat ha', sw32_ofNat hb', toNat64 hl'] at hq
  exact hq

theorem bupAt_tr {P : Prims} (hP : PrimsOk P D) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    RelCT isa (LRel D rbs wbs) (bitUnpackAt P v len a b f) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  refine callP_tr hP.bitUnpack.ver.1 hP.bitUnpack.ver.2.1 (bupArgs_ok ha' hb' hl' hc)
    fun x y x1 y1 R ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, bupPre hP.bitUnpack.hS (At.of R.lx hmx kx) hp hl hc hAx,
        bupPre hP.bitUnpack.hS (At.of R.ly hmy ky) hp hl hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_append (R.lx.cR i1) (covers_wr (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact covers_append (R.ly.cR i1) (covers_wr (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := argsIn5 hAx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := argsIn5 hAy
  sig_pub [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hy1, hy2, hy3, hy4, hy5, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `HintBitPack` -/

theorem hbpArgs_ok {bs : List (Reg × Nat)} {h y : Ptr} {hlen ω len : Nat} (h1 : hlen < 2 ^ 32) (h2 : ω < 2 ^ 32) (h3 : len < 2 ^ 32)
    (hc : rwChk bs wbs h (hlen * 4) y len = true) :
    [Arg.ptr h, .imm hlen, .imm ω, .ptr y, .imm len].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true h1, decide_eq_true h2, decide_eq_true h3]

theorem hintParams_lt {ω k : Nat} (h : (ω, k) ∈ hintParams) : ω < 2 ^ 32 ∧ ω + k < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hbpPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {h y : Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (hA : ArgsIn [.ptr h, .imm (256 * k), .imm ω, .ptr y, .imm (ω + k)] s s1)
    (hones : hintOnes (hintAt s.mem (pa s h) k) ≤ ω) :
    (hintBitPackContract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s h, 256 * k * 4⟩] [⟨pa s y, ω + k⟩]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  have hD : 8 ≤ D := by omega
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  have hwf := ce_wfS (ws := [64, 64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨pa s h, 256 * k * 4⟩]
    [⟨pa s y, ω + k⟩]
  have ek : ω + k - ω = k := by omega
  have i1' : inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega]; exact i1
  sig_pre [hintBitPackContract, hintBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, sw32_ofNat h1, toNat64 h2, toNat64 h3, ek]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hp, by omega, trivial,
    by rw [A.hint i1' hD]; exact hones⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [⟨pa s h, 256 * k * 4⟩, ⟨pa s y, ω + k⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem hbpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {h y : Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (hones : hintOnes (hintAt s.mem (pa s h) k) ≤ ω) :
    WP isa (hintBitPackAt P h (256 * k) ω y (ω + k)) s fun s' => PPostB D s s' [(y, ω + k)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s y) (ω + k) = hintBitPack ω k (hintAt s.mem (pa s h) k) := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.hintBitPack.hS; omega
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  have ek : ω + k - ω = k := by omega
  have i1' : inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega]; exact i1
  refine WP.mono (callP_ok hP.hintBitPack.ver.1 hP.hintBitPack.nosp hP.hintBitPack.depth L.dsm
    (hbpArgs_ok h3 h1 h2 hc) (fun s1 hA hm k => hbpPre hP.hintBitPack.hS (At.of L hm k) hp hc hA hones)
    (covers_append (L.cR i1) (covers_wr (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k', s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k'
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  sig_post [hintBitPackContract, hintBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e3, e4, e5, Arg.val, hm₂, sw32_ofNat h1, toNat64 h2, ek, A.hint i1' hD] at hq
  exact hq

/-- Two runs leak the same when their hints (as the `u32`s at `h`) agree. -/
theorem hbpAt_tr {P : Prims} (hP : PrimsOk P D) {h y : Ptr} {ω k : Nat} (hp : (ω, k) ∈ hintParams)
    (hc : rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true) :
    RelCT isa (fun x z => LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (pa z h) i).toNat))
      (hintBitPackAt P h (256 * k) ω y (ω + k)) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.hintBitPack.hS; omega
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  refine callP_tr hP.hintBitPack.ver.1 hP.hintBitPack.ver.2.1 (hbpArgs_ok h3 h1 h2 hc)
    fun x z x1 z1 ⟨R, ox, oz, hl⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAz, hmz⟩, kz⟩ =>
      ⟨_, _, _, _, hbpPre hP.hintBitPack.hS (At.of R.lx hmx kx) hp hc hAx ox,
        hbpPre hP.hintBitPack.hS (At.of R.ly hmz kz) hp hc hAz oz, ?_,
        by rw [kx.2.1, kx.2.2]; exact covers_append (R.lx.cR i1) (covers_wr (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [kz.2.1, kz.2.2]; exact covers_append (R.ly.cR i1) (covers_wr (R.ly.cW w1)),
        by rw [kz.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmz kz).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := argsIn5 hAx
  obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := argsIn5 hAz
  have Ax := At.of R.lx hmx kx
  have Az := At.of R.ly hmz kz
  sig_pub [hintBitPackContract, hintBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hz1, hz2, hz3, hz4, hz5, Arg.val, toNat64 h3, Ax.coeffs (len := 256 * k) i1 hD,
    Az.coeffs (len := 256 * k) i1 hD, hl]
  simp only [Ax.rsp, Az.rsp, R.rsp, R.pa i1, R.pa i2, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign
