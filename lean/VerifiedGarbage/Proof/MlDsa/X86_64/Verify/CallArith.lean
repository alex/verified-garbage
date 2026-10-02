import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Entry

/-!
# ML-DSA verification on x86-64: calls of the arithmetic primitives

For each call of `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` (`ipAt`),
`vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` and `vg_mldsa_sub`: what
it needs of the layout (a check evaluated on the pointers, `…Chk`), what it
does (`…_ok`), and that two runs whose layout registers agree leak the same
(`…_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def ipChk (bs : List (Reg × Nat)) (wbs : List (Reg × Nat)) (f : Ptr) : Bool :=
  sepB bs f 1024 (sc oSS) 1024 && inB bs f 1024 && inB bs (sc oSS) 1024 && inB wbs f 1024 && inB wbs (sc oSS) 1024

abbrev ipArgs (f : Ptr) : List (Reg × Arg) := [(.rdi, .ptr f), (.rsi, .ptr (sc oSS))]

theorem ip_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {f : Ptr} (hc : ipChk bs wbs f = true) :
    ∀ a ∈ ipArgs f, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [ipChk, Bool.and_eq_true] at hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L hc.1.1.1.2, by decide⟩, ⟨ptr_ok L hc.1.1.2, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f : Ptr}
  (hc : ipChk (rbs ++ wbs) wbs f = true)
include L hc

theorem ip_cov : Covers ([] ++ [⟨pa s f, 1024⟩, ⟨pa s (sc oSS), 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s f, 1024⟩, ⟨pa s (sc oSS), 1024⟩] s.wr := by
  simp only [ipChk, Bool.and_eq_true] at hc
  exact ⟨covers_wr (covers_cons (L.cW hc.1.2) (L.cW hc.2)), covers_cons (L.cW hc.1.2) (L.cW hc.2)⟩

theorem ip_pre {t : Poly → Poly} (hr : Reduced s.mem (pa s f)) {s1 : State} (h1 : Args (ipArgs f) s s1) :
    (inPlaceContract X86_64.abi (t : Poly → Poly) 16).pre
      (s1.callEntry.withRegions [] [⟨pa s f, 1024⟩, ⟨pa s (sc oSS), 1024⟩]) := by
  simp only [ipChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, _⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s f := h1.r0
  have g2 : s1.gpr .rsi = pa s (sc oSS) := h1.r1
  sig_pre [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2, L.stk16 c3, L.nwp c2, L.nwp c3,
    L.wreduced c2 _ hr⟩

end

theorem ipAt_ok {t : Poly → Poly} {n : String} {c : Prog isa} (C : CalleeOk c (inPlaceContract X86_64.abi t 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true)
    (hr : Reduced s.mem (pa s f)) :
    WP isa (callAt n c (ipArgs f)) s fun s' => PPostB s s' [(f, 1024), (sc oSS, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (ip_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => ip_pre L hc hr h1) (ip_cov L hc).1 (ip_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have g1 : s1.gpr .rdi = pa s f := h1.r0
  have c2 : inB (rbs ++ wbs) f 1024 = true := by
    simp only [ipChk, Bool.and_eq_true] at hc; exact hc.1.1.1.2
  sig_post [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [g1, hm, h1.rsp, h1.1.2, L.wpolyAt c2] at hq
  exact hq

theorem ipAt_tr {t : Poly → Poly} {n : String} {c : Prog isa} (C : CalleeOk c (inPlaceContract X86_64.abi t 16))
    {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f) ∧ SameB x y) :
    RelCT isa P (callAt n c (ipArgs f)) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (ip_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  · intro x y x1 y1 hp h1 h2
    obtain ⟨Lx, Ly, rx, ry, e⟩ := hP x y hp
    refine ⟨_, _, _, _, ip_pre Lx hc rx h1, ip_pre Ly hc ry h2, ?_, (ip_cov Lx hc).1, (ip_cov Lx hc).2,
      (ip_cov Ly hc).1, (ip_cov Ly hc).2, e.2⟩
    have hb : f.1 ∈ bases := by
      simp only [ipChk, Bool.and_eq_true] at hc; exact ptr_bs hS hc.1.1.1.2
    sig_pub [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
    rw [h1.r0, h2.r0, h1.r1,
      h2.r1, h1.rsp, h2.rsp]
    exact ⟨by rw [e.2], by simp only [Arg.val]; rw [e.pa hb], by simp only [Arg.val]; rw [e.pa (by decide)]⟩


/-! ## Products -/

def mulChk (bs wbs : List (Reg × Nat)) (h f g : Ptr) : Bool :=
  sepB bs h 1024 f 1024 && sepB bs h 1024 g 1024 && inB bs h 1024 && inB bs f 1024 && inB bs g 1024 &&
    inB wbs h 1024

abbrev mulArgs (h f g : Ptr) : List (Reg × Arg) := [(.rdi, .ptr h), (.rsi, .ptr f), (.rdx, .ptr g)]

theorem mul_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {h f g : Ptr} (hc : mulChk bs wbs h f g = true) :
    ∀ a ∈ mulArgs h f g, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c3, by decide⟩, ⟨ptr_ok L c4, by decide⟩, ⟨ptr_ok L c5, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {h f g : Ptr}
  (hc : mulChk (rbs ++ wbs) wbs h f g = true)
include L hc

theorem mul_cov : Covers ([⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] ++ [⟨pa s h, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s h, 1024⟩] s.wr := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  exact ⟨covers_append (covers_cons (L.cR c4) (L.cR c5)) (L.cR c3), L.cW c6⟩

theorem mul_pre (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) {s1 : State}
    (h1 : Args (mulArgs h f g) s s1) :
    (mulContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] [⟨pa s h, 1024⟩]) := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s h := h1.r0
  have g2 : s1.gpr .rsi = pa s f := h1.r1
  have g3 : s1.gpr .rdx = pa s g := h1.r2
  sig_pre [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, g3, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.disj c2, L.ret8 c3, L.ret8 c4, L.ret8 c5, L.stk16 c3, L.stk16 c4,
    L.stk16 c5, L.nwp c3, L.nwp c4, L.nwp c5, L.wreduced c4 _ hf, L.wreduced c5 _ hg⟩

theorem mulAdd_pre (hh : Reduced s.mem (pa s h)) (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g))
    {s1 : State} (h1 : Args (mulArgs h f g) s s1) :
    (mulAddContract X86_64.abi 16).pre
      (s1.callEntry.withRegions [⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] [⟨pa s h, 1024⟩]) := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s h := h1.r0
  have g2 : s1.gpr .rsi = pa s f := h1.r1
  have g3 : s1.gpr .rdx = pa s g := h1.r2
  sig_pre [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, g3, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.disj c2, L.ret8 c3, L.ret8 c4, L.ret8 c5, L.stk16 c3, L.stk16 c4,
    L.stk16 c5, L.nwp c3, L.nwp c4, L.nwp c5, L.wreduced c3 _ hh, L.wreduced c4 _ hf, L.wreduced c5 _ hg⟩

end

theorem mulAt_ok {P : Prims} (C : CalleeOk P.mul (mulContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : Lay rbs wbs s) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true)
    (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) :
    WP isa (mulAt P h f g) s fun s' => PPostB s s' [(h, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s h) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (mul_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => mul_pre L hc hf hg h1) (mul_cov L hc).1 (mul_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c4⟩, c5⟩, _⟩ := hc
  sig_post [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wpolyAt c4, L.wpolyAt c5] at hq
  exact hq

theorem mulAddAt_ok {P : Prims} (C : CalleeOk P.mulAdd (mulAddContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : Lay rbs wbs s) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true)
    (hh : Reduced s.mem (pa s h)) (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) :
    WP isa (mulAddAt P h f g) s fun s' => PPostB s s' [(h, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s h) (add (polyAt s.mem (pa s h)) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g)))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (mul_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => mulAdd_pre L hc hh hf hg h1) (mul_cov L hc).1 (mul_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_post [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wpolyAt c3, L.wpolyAt c4, L.wpolyAt c5] at hq
  exact hq

theorem mul_pub {x y x1 y1 : State} {h f g : Ptr} (hb : h.1 ∈ bases ∧ f.1 ∈ bases ∧ g.1 ∈ bases) (e : SameB x y)
    (h1 : Args (mulArgs h f g) x x1) (h2 : Args (mulArgs h f g) y y1) :
    x1.gpr .rsp - 8 = y1.gpr .rsp - 8 ∧ x1.gpr .rdi = y1.gpr .rdi ∧ x1.gpr .rsi = y1.gpr .rsi ∧
      x1.gpr .rdx = y1.gpr .rdx := by
  rw [h1.r0, h1.r1, h1.r2, h2.r0, h2.r1, h2.r2]
  simp only [Arg.val]
  refine ⟨?_, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  rw [h1.rsp, h2.rsp, e.2]

theorem mulAt_tr {P : Prims} (C : CalleeOk P.mul (mulContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : LayOk (rbs ++ wbs)) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g)) ∧ SameB x y) :
    RelCT isa Q (mulAt P h f g) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (mul_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, mul_pre Lx hc rx.1 rx.2 h1, mul_pre Ly hc ry.1 ry.2 h2, ?_, (mul_cov Lx hc).1, (mul_cov Lx hc).2,
    (mul_cov Ly hc).1, (mul_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  sig_pub [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  exact mul_pub ⟨ptr_bs hS c3, ptr_bs hS c4, ptr_bs hS c5⟩ e h1 h2

theorem mulAddAt_tr {P : Prims} (C : CalleeOk P.mulAdd (mulAddContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : LayOk (rbs ++ wbs)) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧
      (Reduced x.mem (pa x h) ∧ Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y h) ∧ Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g)) ∧ SameB x y) :
    RelCT isa Q (mulAddAt P h f g) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (mul_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, mulAdd_pre Lx hc rx.1 rx.2.1 rx.2.2 h1, mulAdd_pre Ly hc ry.1 ry.2.1 ry.2.2 h2, ?_,
    (mul_cov Lx hc).1, (mul_cov Lx hc).2, (mul_cov Ly hc).1, (mul_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  sig_pub [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  exact mul_pub ⟨ptr_bs hS c3, ptr_bs hS c4, ptr_bs hS c5⟩ e h1 h2

/-! ## Subtraction -/

def subChk (bs wbs : List (Reg × Nat)) (f g : Ptr) : Bool :=
  sepB bs f 1024 g 1024 && inB bs f 1024 && inB bs g 1024 && inB wbs f 1024

abbrev subArgs (f g : Ptr) : List (Reg × Arg) := [(.rdi, .ptr f), (.rsi, .ptr g)]

theorem sub_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {f g : Ptr} (hc : subChk bs wbs f g = true) :
    ∀ a ∈ subArgs f g, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c2, by decide⟩, ⟨ptr_ok L c3, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f g : Ptr}
  (hc : subChk (rbs ++ wbs) wbs f g = true)
include L hc

theorem sub_cov : Covers ([⟨pa s g, 1024⟩] ++ [⟨pa s f, 1024⟩]) (s.rd ++ s.wr) ∧ Covers [⟨pa s f, 1024⟩] s.wr := by
  simp only [subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨covers_append (L.cR c3) (L.cR c2), L.cW c4⟩

theorem sub_pre (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) {s1 : State}
    (h1 : Args (subArgs f g) s s1) :
    (subContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨pa s g, 1024⟩] [⟨pa s f, 1024⟩]) := by
  simp only [subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s f := h1.r0
  have g2 : s1.gpr .rsi = pa s g := h1.r1
  sig_pre [subContract, accSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2, L.stk16 c3, L.nwp c2, L.nwp c3,
    L.wreduced c2 _ hf, L.wreduced c3 _ hg⟩

end

theorem subAt_ok {P : Prims} (C : CalleeOk P.sub (subContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : Lay rbs wbs s) {f g : Ptr} (hc : subChk (rbs ++ wbs) wbs f g = true)
    (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) :
    WP isa (subAt P f g) s fun s' => PPostB s s' [(f, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s f) (sub (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (sub_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => sub_pre L hc hf hg h1) (sub_cov L hc).1 (sub_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  sig_post [subContract, accSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wpolyAt c2, L.wpolyAt c3] at hq
  exact hq

theorem subAt_tr {P : Prims} (C : CalleeOk P.sub (subContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : LayOk (rbs ++ wbs)) {f g : Ptr} (hc : subChk (rbs ++ wbs) wbs f g = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g)) ∧ SameB x y) :
    RelCT isa Q (subAt P f g) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (sub_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, sub_pre Lx hc rx.1 rx.2 h1, sub_pre Ly hc ry.1 ry.2 h2, ?_, (sub_cov Lx hc).1, (sub_cov Lx hc).2,
    (sub_cov Ly hc).1, (sub_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [subChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [subContract, accSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h2.r0, h2.r1, h1.rsp, h2.rsp, e.2]
  simp only [Arg.val]
  exact ⟨trivial, e.pa (ptr_bs hS c2), e.pa (ptr_bs hS c3)⟩

end VG.Proof.MlDsa.X86_64.Verify
