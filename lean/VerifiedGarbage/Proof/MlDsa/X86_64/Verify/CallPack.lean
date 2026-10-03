import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallSample

/-!
# ML-DSA verification on x86-64: calls of the rounding and encoding primitives

The calls of `vg_mldsa_use_hint`, `vg_mldsa_simple_bit_pack`,
`vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1`, `vg_mldsa_hint_bit_unpack` and
`vg_mldsa_norm_lt`: what they need of the layout (`…Chk`), what they do
(`…_ok`), and that two runs whose layout registers agree (and, for
`vg_mldsa_hint_bit_unpack`, the encoded hint) leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem gamma2s_lt {g : Nat} (h : g ∈ gamma2s) : g < 2 ^ 31 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide

/-! ## `UseHint` -/

def uhChk (bs wbs : List (Reg × Nat)) (h r out : Ptr) : Bool :=
  sepB bs h 1024 out 1024 && sepB bs r 1024 out 1024 && inB bs h 1024 && inB bs r 1024 && inB bs out 1024 &&
    inB wbs out 1024

abbrev uhArgs (h r : Ptr) (g2 : Nat) (out : Ptr) : List (Reg × Arg) :=
  [(.rdi, .ptr h), (.rsi, .ptr r), (.rdx, .imm g2), (.rcx, .ptr out)]

theorem uh_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {h r out : Ptr} {g2 : Nat} (hg : g2 ∈ gamma2s)
    (hc : uhChk bs wbs h r out = true) : ∀ a ∈ uhArgs h r g2 out, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [uhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c3, by decide⟩, ⟨ptr_ok L c4, by decide⟩, ⟨gamma2s_lt hg, by decide⟩, ⟨ptr_ok L c5, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {h r out : Ptr} {g2 : Nat}
  (hc : uhChk (rbs ++ wbs) wbs h r out = true)
include L hc

theorem uh_cov : Covers ([⟨pa s h, 1024⟩, ⟨pa s r, 1024⟩] ++ [⟨pa s out, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s out, 1024⟩] s.wr := by
  simp only [uhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  exact ⟨Covers.append_left (Covers.cons (L.cR c3) (L.cR c4)) (L.cR c5), L.cW c6⟩

theorem uh_pre (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (pa s r)) {s1 : State} (h1 : Args (uhArgs h r g2 out) s s1) :
    (useHintContract X86_64.abi 16).pre
      (s1.callEntry.withRegions [⟨pa s h, 1024⟩, ⟨pa s r, 1024⟩] [⟨pa s out, 1024⟩]) := by
  simp only [uhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_pre [useHintContract, useHintSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.rsp, h1.1.2]
  simp only [Arg.val]
  rw [imm32 (show g2 < 2 ^ 32 by have := gamma2s_lt hg; omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.disj c2, L.ret8 c3, L.ret8 c4,
    L.ret8 c5, L.stk16 c3, L.stk16 c4, L.stk16 c5, L.nwp c3, L.nwp c4, L.nwp c5, hg, L.wreduced c4 _ hr⟩

end

theorem useHintAt_ok {P : Prims} (C : CalleeOk P.useHint (useHintContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : Lay rbs wbs s) {h r out : Ptr} {g2 : Nat} (hg : g2 ∈ gamma2s)
    (hc : uhChk (rbs ++ wbs) wbs h r out = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (useHintAt P h r g2 out) s fun s' => PPostB s s' [(out, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      NatPolyIs s'.mem (pa s out) (Vector.zipWith (fun hj rj => (useHint g2 hj rj).toNat)
        ((hintAt s.mem (pa s h) 1).headD (Vector.replicate n false)) (polyAt s.mem (pa s r))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (uh_args L.ok hg hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => uh_pre L hc hg hr h1) (uh_cov L hc).1 (uh_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [uhChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, _⟩, _⟩ := hc'
  sig_post [useHintContract, useHintSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [imm32 (show g2 < 2 ^ 32 by have := gamma2s_lt hg; omega), L.whintAt c3, L.wpolyAt c4] at hq
  exact hq

theorem useHintAt_tr {P : Prims} (C : CalleeOk P.useHint (useHintContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : LayOk (rbs ++ wbs)) {h r out : Ptr} {g2 : Nat} (hg : g2 ∈ gamma2s)
    (hc : uhChk (rbs ++ wbs) wbs h r out = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r) ∧ SameB x y) :
    RelCT isa Q (useHintAt P h r g2 out) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (uh_args hS hg hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, uh_pre Lx hc hg rx h1, uh_pre Ly hc hg ry h2, ?_, (uh_cov Lx hc).1, (uh_cov Lx hc).2,
    (uh_cov Ly hc).1, (uh_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [uhChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  sig_pub [useHintContract, useHintSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h2.r0, h2.r1, h2.r2, h2.r3, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (ptr_bs hS c3), e.pa (ptr_bs hS c4), by first | rfl | trivial, e.pa (ptr_bs hS c5)⟩

/-! ## `SimpleBitPack` -/

def sbpChk (bs wbs : List (Reg × Nat)) (f out : Ptr) (len : Nat) : Bool :=
  sepB bs f 1024 out len && inB bs f 1024 && inB bs out len && inB wbs out len

abbrev sbpArgs (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.rdi, .ptr f), (.rsi, .imm b), (.rdx, .ptr out), (.rcx, .imm len)]

theorem sbp_small {b len : Nat} (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) :
    b < 2 ^ 31 ∧ len < 2 ^ 31 := by
  simp only [simpleBitPackBounds, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hl
  rcases hb with rfl | rfl | rfl <;> decide

theorem sbp_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : sbpChk bs wbs f out len = true) :
    ∀ a ∈ sbpArgs f b out len, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [sbpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  have := sbp_small hb hl
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c2, by decide⟩, ⟨this.1, by decide⟩, ⟨ptr_ok L c3, by decide⟩, ⟨this.2, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f out : Ptr} {b len : Nat}
  (hc : sbpChk (rbs ++ wbs) wbs f out len = true)
include L hc

theorem sbp_cov : Covers ([⟨pa s f, 1024⟩] ++ [⟨pa s out, len⟩]) (s.rd ++ s.wr) ∧ Covers [⟨pa s out, len⟩] s.wr := by
  simp only [sbpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c2) (L.cR c3), L.cW c4⟩

theorem sbp_pre (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b)
    (hf : ∀ i < n, (coeffAt s.mem (pa s f) i).toNat ≤ b) {s1 : State} (h1 : Args (sbpArgs f b out len) s s1) :
    (simpleBitPackContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨pa s f, 1024⟩] [⟨pa s out, len⟩]) := by
  simp only [sbpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  have hs := sbp_small hb hl
  sig_pre [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.rsp, h1.1.2]
  simp only [Arg.val]
  rw [imm32 (show b < 2 ^ 32 by omega), imm64 (show len < 2 ^ 64 by omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2,
    L.stk16 c3, L.nwp c2, L.nwp c3, hb, hl, fun i hi => by rw [L.wcoeffAt c2 _ hi]; exact hf i hi⟩

end

theorem sbpAt_ok {P : Prims} (C : CalleeOk P.simpleBitPack (simpleBitPackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : sbpChk (rbs ++ wbs) wbs f out len = true)
    (hf : ∀ i < n, (coeffAt s.mem (pa s f) i).toNat ≤ b) :
    WP isa (sbpAt P f b out len) s fun s' => PPostB s s' [(out, len)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s out) len = simpleBitPack (natPolyAt s.mem (pa s f)) b := by
  have hs := sbp_small hb hl
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (sbp_args L.ok hb hl hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => sbp_pre L hc hb hl hf h1) (sbp_cov L hc).1 (sbp_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [sbpChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, _⟩, _⟩ := hc'
  sig_post [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [imm32 (show b < 2 ^ 32 by omega), imm64 (show len < 2 ^ 64 by omega), L.wnatPolyAt c2] at hq
  exact hq

theorem sbpAt_tr {P : Prims} (C : CalleeOk P.simpleBitPack (simpleBitPackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : sbpChk (rbs ++ wbs) wbs f out len = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ (∀ i < n, (coeffAt x.mem (pa x f) i).toNat ≤ b) ∧
      (∀ i < n, (coeffAt y.mem (pa y f) i).toNat ≤ b) ∧ SameB x y) :
    RelCT isa Q (sbpAt P f b out len) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (sbp_args hS hb hl hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, sbp_pre Lx hc hb hl rx h1, sbp_pre Ly hc hb hl ry h2, ?_, (sbp_cov Lx hc).1, (sbp_cov Lx hc).2,
    (sbp_cov Ly hc).1, (sbp_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [sbpChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h2.r0, h2.r1, h2.r2, h2.r3, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (ptr_bs hS c2), by first | rfl | trivial, e.pa (ptr_bs hS c3), by first | rfl | trivial⟩

/-! ## `BitUnpack` -/

def buChk (bs wbs : List (Reg × Nat)) (v : Ptr) (len : Nat) (f : Ptr) : Bool :=
  sepB bs v len f 1024 && inB bs v len && inB bs f 1024 && inB wbs f 1024

abbrev buArgs (v : Ptr) (len a b : Nat) (f : Ptr) : List (Reg × Arg) :=
  [(.rdi, .ptr v), (.rsi, .imm len), (.rdx, .imm a), (.rcx, .imm b), (.r8, .ptr f)]

theorem bu_small {a b len : Nat} (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) :
    a < 2 ^ 31 ∧ b < 2 ^ 31 ∧ len < 2 ^ 31 := by
  simp only [bitPackParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  subst hl
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bu_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {v f : Ptr} {len a b : Nat}
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : buChk bs wbs v len f = true) :
    ∀ x ∈ buArgs v len a b f, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [buChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  have := bu_small hab hl
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c2, by decide⟩, ⟨this.2.2, by decide⟩, ⟨this.1, by decide⟩, ⟨this.2.1, by decide⟩,
    ⟨ptr_ok L c3, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {v f : Ptr} {len a b : Nat}
  (hc : buChk (rbs ++ wbs) wbs v len f = true)
include L hc

theorem bu_cov : Covers ([⟨pa s v, len⟩] ++ [⟨pa s f, 1024⟩]) (s.rd ++ s.wr) ∧ Covers [⟨pa s f, 1024⟩] s.wr := by
  simp only [buChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c2) (L.cR c3), L.cW c4⟩

theorem bu_pre (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) {s1 : State}
    (h1 : Args (buArgs v len a b f) s s1) :
    (bitUnpackContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨pa s v, len⟩] [⟨pa s f, 1024⟩]) := by
  simp only [buChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  have hs := bu_small hab hl
  sig_pre [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.rsp]
  simp only [Arg.val]
  rw [imm32 (show a < 2 ^ 32 by omega), imm32 (show b < 2 ^ 32 by omega), imm64 (show len < 2 ^ 64 by omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2,
    L.stk16 c3, L.nwp c2, L.nwp c3, hab, hl⟩

end

theorem bitUnpackAt_ok {P : Prims} (C : CalleeOk P.bitUnpack (bitUnpackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {v f : Ptr} {len a b : Nat}
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : buChk (rbs ++ wbs) wbs v len f = true) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => PPostB s s' [(f, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s f) (toRq (bitUnpack (bytesAt s.mem (pa s v) len) a b)) := by
  have hs := bu_small hab hl
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (bu_args L.ok hab hl hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => bu_pre L hc hab hl h1) (bu_cov L hc).1 (bu_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [buChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, _⟩, _⟩ := hc'
  sig_post [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [imm32 (show a < 2 ^ 32 by omega), imm32 (show b < 2 ^ 32 by omega), imm64 (show len < 2 ^ 64 by omega),
    L.wbytesAt c2] at hq
  exact hq

theorem bitUnpackAt_tr {P : Prims} (C : CalleeOk P.bitUnpack (bitUnpackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {v f : Ptr} {len a b : Nat}
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : buChk (rbs ++ wbs) wbs v len f = true)
    {Q : State → State → Prop} (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ SameB x y) :
    RelCT isa Q (bitUnpackAt P v len a b f) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (bu_args hS hab hl hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, bu_pre Lx hc hab hl h1, bu_pre Ly hc hab hl h2, ?_, (bu_cov Lx hc).1, (bu_cov Lx hc).2,
    (bu_cov Ly hc).1, (bu_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [buChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (ptr_bs hS c2), by first | rfl | trivial, by first | rfl | trivial,
    by first | rfl | trivial, e.pa (ptr_bs hS c3)⟩

/-! ## `t₁ · 2ᵈ` -/

def t1Chk (bs wbs : List (Reg × Nat)) (v f : Ptr) : Bool :=
  sepB bs v 320 f 1024 && inB bs v 320 && inB bs f 1024 && inB wbs f 1024

abbrev t1Args (v f : Ptr) : List (Reg × Arg) := [(.rdi, .ptr v), (.rsi, .ptr f)]

theorem t1_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {v f : Ptr} (hc : t1Chk bs wbs v f = true) :
    ∀ x ∈ t1Args v f, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [t1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c2, by decide⟩, ⟨ptr_ok L c3, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {v f : Ptr}
  (hc : t1Chk (rbs ++ wbs) wbs v f = true)
include L hc

theorem t1_cov : Covers ([⟨pa s v, 320⟩] ++ [⟨pa s f, 1024⟩]) (s.rd ++ s.wr) ∧ Covers [⟨pa s f, 1024⟩] s.wr := by
  simp only [t1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c2) (L.cR c3), L.cW c4⟩

theorem t1_pre {s1 : State} (h1 : Args (t1Args v f) s s1) :
    (unpackT1Contract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨pa s v, 320⟩] [⟨pa s f, 1024⟩]) := by
  simp only [t1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  sig_pre [unpackT1Contract, unpackT1Sig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.rsp]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2, L.stk16 c3, L.nwp c2, L.nwp c3⟩

end

theorem unpackT1At_ok {P : Prims} (C : CalleeOk P.unpackT1 (unpackT1Contract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {v f : Ptr} (hc : t1Chk (rbs ++ wbs) wbs v f = true) :
    WP isa (unpackT1At P v f) s fun s' => PPostB s s' [(f, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s f) ((simpleBitUnpack (bytesAt s.mem (pa s v) 320) t1Max).map
        fun c => ofInt (c * 2 ^ d : Nat)) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (t1_args L.ok hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => t1_pre L hc h1) (t1_cov L hc).1 (t1_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [t1Chk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, _⟩, _⟩ := hc'
  sig_post [unpackT1Contract, unpackT1Sig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wbytesAt c2] at hq
  exact hq

theorem unpackT1At_tr {P : Prims} (C : CalleeOk P.unpackT1 (unpackT1Contract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {v f : Ptr} (hc : t1Chk (rbs ++ wbs) wbs v f = true)
    {Q : State → State → Prop} (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ SameB x y) :
    RelCT isa Q (unpackT1At P v f) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (t1_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, t1_pre Lx hc h1, t1_pre Ly hc h2, ?_, (t1_cov Lx hc).1, (t1_cov Lx hc).2,
    (t1_cov Ly hc).1, (t1_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [t1Chk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [unpackT1Contract, unpackT1Sig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h2.r0, h2.r1, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (ptr_bs hS c2), e.pa (ptr_bs hS c3)⟩

/-! ## `HintBitUnpack` -/

def huChk (bs wbs : List (Reg × Nat)) (y : Ptr) (len : Nat) (h : Ptr) (hlen : Nat) : Bool :=
  sepB bs y len h (hlen * 4) && inB bs y len && inB bs h (hlen * 4) && inB wbs h (hlen * 4)

abbrev huArgs (y : Ptr) (len omega : Nat) (h : Ptr) (hlen : Nat) : List (Reg × Arg) :=
  [(.rdi, .ptr y), (.rsi, .imm len), (.rdx, .imm omega), (.rcx, .ptr h), (.r8, .imm hlen)]

/-- The arguments of `vg_mldsa_hint_bit_unpack` for the parameters `(ω, k)`. -/
def HuPar (len omega hlen : Nat) : Prop :=
  (omega, len - omega) ∈ hintParams ∧ omega ≤ len ∧ hlen = 256 * (len - omega)

instance (len omega hlen : Nat) : Decidable (HuPar len omega hlen) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem hu_small {len omega hlen : Nat} (h : HuPar len omega hlen) :
    len < 2 ^ 31 ∧ omega < 2 ^ 31 ∧ hlen < 2 ^ 31 := by
  obtain ⟨hp, hl, hh⟩ := h
  simp only [hintParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  omega

theorem hu_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {y h : Ptr} {len omega hlen : Nat}
    (hp : HuPar len omega hlen) (hc : huChk bs wbs y len h hlen = true) :
    ∀ x ∈ huArgs y len omega h hlen, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [huChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  have := hu_small hp
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c2, by decide⟩, ⟨this.1, by decide⟩, ⟨this.2.1, by decide⟩, ⟨ptr_ok L c3, by decide⟩,
    ⟨this.2.2, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {y h : Ptr} {len omega hlen : Nat}
  (hc : huChk (rbs ++ wbs) wbs y len h hlen = true)
include L hc

theorem hu_cov : Covers ([⟨pa s y, len⟩] ++ [⟨pa s h, hlen * 4⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s h, hlen * 4⟩] s.wr := by
  simp only [huChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c2) (L.cR c3), L.cW c4⟩

theorem hu_pre (hp : HuPar len omega hlen) {s1 : State} (h1 : Args (huArgs y len omega h hlen) s s1) :
    (hintBitUnpackContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨pa s y, len⟩] [⟨pa s h, hlen * 4⟩]) := by
  simp only [huChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  have hs := hu_small hp
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.rsp]
  simp only [Arg.val]
  rw [imm64 (show len < 2 ^ 64 by omega), imm32 (show omega < 2 ^ 32 by omega), imm64 (show hlen < 2 ^ 64 by omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2,
    L.stk16 c3, L.nwp c2, L.nwp c3, hp.1, hp.2.1, hp.2.2⟩

end

theorem hintUnpackAt_ok {P : Prims} (C : CalleeOk P.hintUnpack (hintBitUnpackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {y h : Ptr} {len omega hlen : Nat}
    (hp : HuPar len omega hlen) (hc : huChk (rbs ++ wbs) wbs y len h hlen = true) :
    WP isa (hintUnpackAt P y len omega h hlen) s fun s' => PPostB s s' [(h, hlen * 4)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      match hintBitUnpack omega (len - omega) (bytesAt s.mem (pa s y) len) with
      | some hint => res s' = 1 ∧ HintIs s'.mem (pa s h) (len - omega) hint
      | none => res s' = 0 := by
  have hs := hu_small hp
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (hu_args L.ok hp hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => hu_pre L hc hp h1) (hu_cov L hc).1 (hu_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, hg, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [huChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, _⟩, _⟩ := hc'
  sig_post [hintBitUnpackContract, hintBitUnpackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, hm, h1.rsp, h1.1.2, hg _ (by decide)] at hq
  simp only [Arg.val] at hq
  rw [imm64 (show len < 2 ^ 64 by omega), imm32 (show omega < 2 ^ 32 by omega), L.wbytesAt c2] at hq
  exact hq

theorem hintUnpackAt_tr {P : Prims} (C : CalleeOk P.hintUnpack (hintBitUnpackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {y h : Ptr} {len omega hlen : Nat}
    (hp : HuPar len omega hlen) (hc : huChk (rbs ++ wbs) wbs y len h hlen = true)
    {Q : State → State → Prop} (hQ : ∀ x x', Q x x' → Lay rbs wbs x ∧ Lay rbs wbs x' ∧ SameB x x' ∧
      bytesAt x.mem (pa x y) len = bytesAt x'.mem (pa x' y) len) :
    RelCT isa Q (hintUnpackAt P y len omega h hlen) fun _ _ => True := by
  have hs := hu_small hp
  refine callAt_tr C.correct C.ct (hu_args hS hp hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x x' x1 y1 hq h1 h2
  obtain ⟨Lx, Ly, e, eb⟩ := hQ x x' hq
  refine ⟨_, _, _, _, hu_pre Lx hc hp h1, hu_pre Ly hc hp h2, ?_, (hu_cov Lx hc).1, (hu_cov Lx hc).2,
    (hu_cov Ly hc).1, (hu_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [huChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h1.1.2, h2.1.2, h1.rsp, h2.rsp]
  simp only [Arg.val]
  rw [imm64 (show len < 2 ^ 64 by omega), Lx.wbytesAt c2, Ly.wbytesAt c2, eb]
  exact ⟨by rw [e.2], rfl, e.pa (ptr_bs hS c2), by first | rfl | trivial, by first | rfl | trivial,
    e.pa (ptr_bs hS c3), by first | rfl | trivial⟩

/-! ## The norm -/

def nlChk (bs : List (Reg × Nat)) (f : Ptr) : Bool := inB bs f 1024

abbrev nlArgs (f : Ptr) (bound : Nat) : List (Reg × Arg) := [(.rdi, .ptr f), (.rsi, .imm bound)]

theorem nl_args {bs : List (Reg × Nat)} (L : LayOk bs) {f : Ptr} {bound : Nat} (hb : bound < 2 ^ 31)
    (hc : nlChk bs f = true) : ∀ x ∈ nlArgs f bound, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L hc, by decide⟩, ⟨hb, by decide⟩⟩

theorem nl_pre {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f : Ptr} {bound : Nat}
    (hc : nlChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (pa s f)) {s1 : State} (h1 : Args (nlArgs f bound) s s1) :
    (normLtContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨pa s f, 1024⟩] []) := by
  sig_pre [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, L.ret8 hc, L.stk16 hc, L.nwp hc, L.wreduced hc _ hr⟩

theorem normLtAt_ok {P : Prims} (C : CalleeOk P.normLt (normLtContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f : Ptr} {bound : Nat} (hb : bound < 2 ^ 31)
    (hc : nlChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (normLtAt P f bound) s fun s' => PPostB s s' [] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      res s' = if normRq [polyAt s.mem (pa s f)] < bound then 1 else 0 := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (nl_args L.ok hb hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => nl_pre L hc hr h1) (Covers.append_left (L.cR hc) Covers.nil) Covers.nil)
    fun s' ⟨hP, s1, h1, s₂, hm, hg, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  sig_post [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.rsp, h1.1.2, hg _ (by decide)] at hq
  simp only [Arg.val, imm32 (show bound < 2 ^ 32 by omega), L.wpolyAt hc] at hq
  exact hq

theorem normLtAt_tr {P : Prims} (C : CalleeOk P.normLt (normLtContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {f : Ptr} {bound : Nat} (hb : bound < 2 ^ 31)
    (hc : nlChk (rbs ++ wbs) f = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f) ∧ SameB x y) :
    RelCT isa Q (normLtAt P f bound) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (nl_args hS hb hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, nl_pre Lx hc rx h1, nl_pre Ly hc ry h2, ?_, Covers.append_left (Lx.cR hc) Covers.nil, Covers.nil,
    Covers.append_left (Ly.cR hc) Covers.nil, Covers.nil, e.2⟩
  sig_pub [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h2.r0, h2.r1, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (ptr_bs hS hc), by first | rfl | trivial⟩

end VG.Proof.MlDsa.X86_64.Verify
