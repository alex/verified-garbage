import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Entry

/-!
# ML-DSA on AArch64: calls of the arithmetic primitives

Untrusted: everything here is checked by Lean. For each call of
`vg_mldsa_ntt`, `vg_mldsa_inv_ntt` (`ipAt`), `vg_mldsa_multiply_ntt`,
`vg_mldsa_multiply_add_ntt`, `vg_mldsa_add` and `vg_mldsa_sub`: what it
needs of the layout (a check evaluated on the pointers, `…Chk`), what it
does (`…_ok`), and that two runs whose layout registers agree leak the same
(`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa

/-! ## `NTT` and `NTT⁻¹` -/

def ipChk (rbs wbs : List (Reg × Nat)) (f ss : Ptr) : Bool :=
  sepB (rbs ++ wbs) f 1024 ss 1024 && inB (rbs ++ wbs) f 1024 && inB (rbs ++ wbs) ss 1024 && inB wbs f 1024 &&
    inB wbs ss 1024

abbrev ipArgs (f ss : Ptr) : List (Reg × Arg) := [(.x0, .ptr f), (.x1, .ptr ss)]

theorem ip_args {bs : List (Reg × Nat)} (L : LayOk bs) {f ss : Ptr} (c2 : inB bs f 1024 = true)
    (c3 : inB bs ss 1024 = true) : ∀ a ∈ ipArgs f ss, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c2), by decide⟩, ⟨ptr_ok (ptr_bs L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f ss : Ptr}
  (hc : ipChk rbs wbs f ss = true)
include L hc

theorem ip_cov : Covers ([] ++ [⟨pa s f, 1024⟩, ⟨pa s ss, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s f, 1024⟩, ⟨pa s ss, 1024⟩] s.wr := by
  simp only [ipChk, Bool.and_eq_true] at hc
  exact ⟨covers_wr (covers_cons (L.cW hc.1.2) (L.cW hc.2)), covers_cons (L.cW hc.1.2) (L.cW hc.2)⟩

theorem ip_pre {t : Poly → Poly} (hr : Reduced s.mem (pa s f)) {s1 : State} (h1 : Args (ipArgs f ss) s s1) :
    (inPlaceContract AArch64.abi t S).pre (s1.callEntry.withRegions [] [⟨pa s f, 1024⟩, ⟨pa s ss, 1024⟩]) := by
  simp only [ipChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, _⟩, _⟩ := hc
  sig_pre [inPlaceContract, inPlaceSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exact hr

end

theorem ipAtK_ok {S : Nat} (hS : S < 2 ^ 64) {t : Poly → Poly} {n : String} {c : Prog isa}
    (C : CalleeOk S c (inPlaceContract AArch64.abi t S)) {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {f ss : Ptr} (hc : ipChk rbs wbs f ss = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (callAt n c (ipArgs f ss)) s fun s' => PPostB S s s' [(f, 1024), (ss, 1024)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧ PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f))) := by
  have hc' := hc
  simp only [ipChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c2⟩, c3⟩, _⟩, _⟩ := hc'
  refine WP.mono (callAtK_ok hS C (ip_args L.ok c2 c3) (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => ip_pre L hc hr h1)
    (ip_cov L hc).1 (ip_cov L hc).2) fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [inPlaceContract, inPlaceSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.mem h1] at hq
  exact hq

theorem ipAtK_tr {S : Nat} {t : Poly → Poly} {n : String} {c : Prog isa}
    (C : CalleeOk S c (inPlaceContract AArch64.abi t S)) {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs))
    {f ss : Ptr} (hc : ipChk rbs wbs f ss = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f) ∧
      SameB x y) :
    RelCT isa Q (callAt n c (ipArgs f ss)) fun _ _ => True := by
  have hc' := hc
  simp only [ipChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c2⟩, c3⟩, _⟩, _⟩ := hc'
  refine callAtK_tr C (ip_args hB c2 c3) (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨[], [⟨pa x f, 1024⟩, ⟨pa x ss, 1024⟩], ip_pre Lx hc rx h1, ?_, ?_, (ip_cov Lx hc).1, (ip_cov Lx hc).2,
    by rw [e.pa (ptr_bs hB c2), e.pa (ptr_bs hB c3)]; exact (ip_cov Ly hc).1,
    by rw [e.pa (ptr_bs hB c2), e.pa (ptr_bs hB c3)]; exact (ip_cov Ly hc).2⟩
  · rw [e.pa (ptr_bs hB c2), e.pa (ptr_bs hB c3)]; exact ip_pre Ly hc ry h2
  · sig_pub [inPlaceContract, inPlaceSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r0 h2, Args.r1 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa (ptr_bs hB c2), e.pa (ptr_bs hB c3)⟩

/-! ## Products -/

def mulChk (rbs wbs : List (Reg × Nat)) (h f g : Ptr) : Bool :=
  sepB (rbs ++ wbs) h 1024 f 1024 && sepB (rbs ++ wbs) h 1024 g 1024 && inB (rbs ++ wbs) h 1024 &&
    inB (rbs ++ wbs) f 1024 && inB (rbs ++ wbs) g 1024 && inB wbs h 1024

abbrev mulArgs (h f g : Ptr) : List (Reg × Arg) := [(.x0, .ptr h), (.x1, .ptr f), (.x2, .ptr g)]

theorem mul_args {bs : List (Reg × Nat)} (L : LayOk bs) {h f g : Ptr} (c3 : inB bs h 1024 = true)
    (c4 : inB bs f 1024 = true) (c5 : inB bs g 1024 = true) :
    ∀ a ∈ mulArgs h f g, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c3), by decide⟩, ⟨ptr_ok (ptr_bs L c4), by decide⟩, ⟨ptr_ok (ptr_bs L c5), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h f g : Ptr}
  (hc : mulChk rbs wbs h f g = true)
include L hc

theorem mul_cov : Covers ([⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] ++ [⟨pa s h, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s h, 1024⟩] s.wr := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, c4⟩, c5⟩, c6⟩ := hc
  exact ⟨covers_append (covers_cons (L.cR c4) (L.cR c5)) (covers_wr (L.cW c6)), L.cW c6⟩

theorem mul_pre (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) {s1 : State}
    (h1 : Args (mulArgs h f g) s s1) :
    (mulContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] [⟨pa s h, 1024⟩]) := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_pre [mulContract, mulSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exacts [hf, hg]

theorem mulAdd_pre (hh : Reduced s.mem (pa s h)) (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g))
    {s1 : State} (h1 : Args (mulArgs h f g) s s1) :
    (mulAddContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] [⟨pa s h, 1024⟩]) := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_pre [mulAddContract, mulSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exacts [hh, hf, hg]

end

theorem mulAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.mul (mulContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h f g : Ptr} (hc : mulChk rbs wbs h f g = true)
    (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) :
    WP isa (mulAt P h f g) s fun s' => PPostB S s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s h) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  have hc' := hc
  simp only [mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  refine WP.mono (callAtK_ok hS C (mul_args L.ok c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => mul_pre L hc hf hg h1)
    (mul_cov L hc).1 (mul_cov L hc).2) fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [mulContract, mulSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  exact hq

theorem mulAddAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.mulAdd (mulAddContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h f g : Ptr} (hc : mulChk rbs wbs h f g = true)
    (hh : Reduced s.mem (pa s h)) (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) :
    WP isa (mulAddAt P h f g) s fun s' => PPostB S s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s h) (add (polyAt s.mem (pa s h)) (multiplyNTT (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g)))) := by
  have hc' := hc
  simp only [mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  refine WP.mono (callAtK_ok hS C (mul_args L.ok c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => mulAdd_pre L hc hh hf hg h1)
    (mul_cov L hc).1 (mul_cov L hc).2) fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [mulAddContract, mulSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  exact hq

theorem mul_pub {x y x1 y1 : State} {h f g : Ptr} (hb : h.1 ∈ bases ∧ f.1 ∈ bases ∧ g.1 ∈ bases) (e : SameB x y)
    (h1 : Args (mulArgs h f g) x x1) (h2 : Args (mulArgs h f g) y y1) :
    x1.sp = y1.sp ∧ x1.gpr .x0 = y1.gpr .x0 ∧ x1.gpr .x1 = y1.gpr .x1 ∧ x1.gpr .x2 = y1.gpr .x2 := by
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2]
  simp only [Arg.val]
  exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩

theorem mulAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.mul (mulContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {h f g : Ptr} (hc : mulChk rbs wbs h f g = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g)) ∧ SameB x y) :
    RelCT isa Q (mulAt P h f g) fun _ _ => True := by
  have hc' := hc
  simp only [mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  have hb : h.1 ∈ bases ∧ f.1 ∈ bases ∧ g.1 ∈ bases := ⟨ptr_bs hB c3, ptr_bs hB c4, ptr_bs hB c5⟩
  refine callAtK_tr C (mul_args hB c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, mul_pre Lx hc rx.1 rx.2 h1, ?_, ?_, (mul_cov Lx hc).1, (mul_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact mul_pre Ly hc ry.1 ry.2 h2
  · sig_pub [mulContract, mulSig, AArch64.abi, VG.AArch64.argRegs]
    exact mul_pub hb e h1 h2
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (mul_cov Ly hc).1
  · rw [e.pa hb.1]; exact (mul_cov Ly hc).2

theorem mulAddAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.mulAdd (mulAddContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {h f g : Ptr} (hc : mulChk rbs wbs h f g = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      (Reduced x.mem (pa x h) ∧ Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y h) ∧ Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g)) ∧ SameB x y) :
    RelCT isa Q (mulAddAt P h f g) fun _ _ => True := by
  have hc' := hc
  simp only [mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  have hb : h.1 ∈ bases ∧ f.1 ∈ bases ∧ g.1 ∈ bases := ⟨ptr_bs hB c3, ptr_bs hB c4, ptr_bs hB c5⟩
  refine callAtK_tr C (mul_args hB c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, mulAdd_pre Lx hc rx.1 rx.2.1 rx.2.2 h1, ?_, ?_, (mul_cov Lx hc).1, (mul_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact mulAdd_pre Ly hc ry.1 ry.2.1 ry.2.2 h2
  · sig_pub [mulAddContract, mulSig, AArch64.abi, VG.AArch64.argRegs]
    exact mul_pub hb e h1 h2
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (mul_cov Ly hc).1
  · rw [e.pa hb.1]; exact (mul_cov Ly hc).2

/-! ## Addition and subtraction -/

def accChk (rbs wbs : List (Reg × Nat)) (f g : Ptr) : Bool :=
  sepB (rbs ++ wbs) f 1024 g 1024 && inB (rbs ++ wbs) f 1024 && inB (rbs ++ wbs) g 1024 && inB wbs f 1024

abbrev accArgs (f g : Ptr) : List (Reg × Arg) := [(.x0, .ptr f), (.x1, .ptr g)]

theorem acc_args {bs : List (Reg × Nat)} (L : LayOk bs) {f g : Ptr} (c2 : inB bs f 1024 = true)
    (c3 : inB bs g 1024 = true) : ∀ a ∈ accArgs f g, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c2), by decide⟩, ⟨ptr_ok (ptr_bs L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f g : Ptr}
  (hc : accChk rbs wbs f g = true)
include L hc

theorem acc_cov : Covers ([⟨pa s g, 1024⟩] ++ [⟨pa s f, 1024⟩]) (s.rd ++ s.wr) ∧ Covers [⟨pa s f, 1024⟩] s.wr := by
  simp only [accChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, _⟩, c3⟩, c4⟩ := hc
  exact ⟨covers_append (L.cR c3) (covers_wr (L.cW c4)), L.cW c4⟩

theorem acc_pre {op : Poly → Poly → Poly} (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) {s1 : State}
    (h1 : Args (accArgs f g) s s1) :
    (accSig.contract AArch64.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := S)).pre
      (s1.callEntry.withRegions [⟨pa s g, 1024⟩] [⟨pa s f, 1024⟩]) := by
  simp only [accChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  sig_pre [accSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exacts [hf, hg]

end

theorem accAtK_ok {S : Nat} (hS : S < 2 ^ 64) {op : Poly → Poly → Poly} {n : String} {c : Prog isa}
    (C : CalleeOk S c (accSig.contract AArch64.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := S)))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f g : Ptr} (hc : accChk rbs wbs f g = true)
    (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) :
    WP isa (callAt n c (accArgs f g)) s fun s' => PPostB S s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s f) (op (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  have hc' := hc
  simp only [accChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  refine WP.mono (callAtK_ok hS C (acc_args L.ok c2 c3) (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => acc_pre L hc hf hg h1)
    (acc_cov L hc).1 (acc_cov L hc).2) fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [accSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem accAtK_tr {S : Nat} {op : Poly → Poly → Poly} {n : String} {c : Prog isa}
    (C : CalleeOk S c (accSig.contract AArch64.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := S)))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {f g : Ptr} (hc : accChk rbs wbs f g = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g)) ∧ SameB x y) :
    RelCT isa Q (callAt n c (accArgs f g)) fun _ _ => True := by
  have hc' := hc
  simp only [accChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  have hb : f.1 ∈ bases ∧ g.1 ∈ bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAtK_tr C (acc_args hB c2 c3) (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, acc_pre Lx hc rx.1 rx.2 h1, ?_, ?_, (acc_cov Lx hc).1, (acc_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2]; exact acc_pre Ly hc ry.1 ry.2 h2
  · sig_pub [accSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r0 h2, Args.r1 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2⟩
  · rw [e.pa hb.1, e.pa hb.2]; exact (acc_cov Ly hc).1
  · rw [e.pa hb.1]; exact (acc_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign
