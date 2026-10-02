import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallSample
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round

/-!
# ML-DSA key generation and verification on AArch64: calls of the rounding primitives

For each call of `vg_mldsa_power2round` and `vg_mldsa_use_hint` (the norm is
in `Proof/MlDsa/AArch64/Call/Round.lean`): what it needs of the layout
(`…Chk`), what it does (`…_ok`), and that two runs whose layout registers
agree leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Power2Round` -/

def p2rChk (rbs wbs : List (Reg × Nat)) (t t1 t0 : Ptr) : Bool :=
  sepB rbs wbs t 1024 t1 1024 && sepB rbs wbs t 1024 t0 1024 && sepB rbs wbs t1 1024 t0 1024 &&
    inB (rbs ++ wbs) t 1024 && inB (rbs ++ wbs) t1 1024 && inB (rbs ++ wbs) t0 1024 && inB wbs t1 1024 &&
    inB wbs t0 1024

abbrev p2rArgs (t t1 t0 : Ptr) : List (Reg × Arg) := [(.x0, .ptr t), (.x1, .ptr t1), (.x2, .ptr t0)]

theorem p2r_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {t t1 t0 : Ptr} (c4 : inB bs t 1024 = true)
    (c5 : inB bs t1 1024 = true) (c6 : inB bs t0 1024 = true) :
    ∀ x ∈ p2rArgs t t1 t0, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩, ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {t t1 t0 : Ptr}
  (hc : p2rChk rbs wbs t t1 t0 = true)
include L hc

theorem p2r_cov : Covers ([⟨pa s t, 1024⟩] ++ [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩] s.wr := by
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨covers_append (L.cR c4) (covers_wr (covers_cons (L.cW c7) (L.cW c8))), covers_cons (L.cW c7) (L.cW c8)⟩

theorem p2r_pre (hr : Reduced s.mem (pa s t)) {s1 : State} (h1 : Args (p2rArgs t t1 t0) s s1) :
    (power2RoundContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s t, 1024⟩] [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩]) := by
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exact hr

end

theorem p2rAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {t t1 t0 : Ptr}
    (hc : p2rChk rbs wbs t t1 t0 = true) (hr : Reduced s.mem (pa s t)) :
    WP isa (power2RoundAt P t t1 t0) s fun s' => PPostB S s s' [(t1, 1024), (t0, 1024)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      NatPolyIs s'.mem (pa s t1) ((polyAt s.mem (pa s t)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s'.mem (pa s t0) ((polyAt s.mem (pa s t)).map fun c => ofInt (power2Round c).2) := by
  have hc' := hc
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (p2r_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => p2r_pre L hc hr h1) (p2r_cov L hc).1 (p2r_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  exact hq

theorem p2rAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {t t1 t0 : Ptr} (hc : p2rChk rbs wbs t t1 t0 = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x t) ∧ Reduced y.mem (pa y t) ∧
      SameB x y) :
    RelCT isa Q (power2RoundAt P t t1 t0) fun _ _ => True := by
  have hc' := hc
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : t.1 ∈ bases ∧ t1.1 ∈ bases ∧ t0.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (p2r_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, p2r_pre Lx hc rx h1, ?_, ?_, (p2r_cov Lx hc).1, (p2r_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact p2r_pre Ly hc ry h2
  · sig_pub [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (p2r_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (p2r_cov Ly hc).2

/-! ## `UseHint` -/

def useHintChk (rbs wbs : List (Reg × Nat)) (h r out : Ptr) : Bool :=
  sepB rbs wbs h 1024 out 1024 && sepB rbs wbs r 1024 out 1024 &&
    inB (rbs ++ wbs) h 1024 && inB (rbs ++ wbs) r 1024 && inB (rbs ++ wbs) out 1024 && inB wbs out 1024

abbrev useHintArgs (h r : Ptr) (g2 : Nat) (out : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr h), (.x1, .ptr r), (.x2, .imm g2), (.x3, .ptr out)]

theorem useHint_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {h r out : Ptr} (g2 : Nat) (c3 : inB bs h 1024 = true)
    (c4 : inB bs r 1024 = true) (c5 : inB bs out 1024 = true) :
    ∀ x ∈ useHintArgs h r g2 out, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c3), by decide⟩, ⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_kept L c5), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h r out : Ptr}
  (hc : useHintChk rbs wbs h r out = true)
include L hc

theorem useHint_cov : Covers ([⟨pa s h, 1024⟩, ⟨pa s r, 1024⟩] ++ [⟨pa s out, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s out, 1024⟩] s.wr := by
  simp only [useHintChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, c3, c4, _, c6⟩ := hc
  exact ⟨covers_append (covers_cons (L.cR c3) (L.cR c4)) (covers_wr (L.cW c6)), L.cW c6⟩

theorem useHint_pre {g2 : Nat} (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (pa s r)) {s1 : State}
    (h1 : Args (useHintArgs h r g2 out) s s1) :
    (useHintContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s h, 1024⟩, ⟨pa s r, 1024⟩] [⟨pa s out, 1024⟩]) := by
  simp only [useHintChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := hc
  sig_pre [useHintContract, useHintSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  rw [imm32 (gamma2_lt hg)]
  cpre L
  exacts [hg, hr]

end

theorem useHintAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.useHint (useHintContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h r out : Ptr}
    (hc : useHintChk rbs wbs h r out = true) {g2 : Nat} (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (pa s r)) :
    WP isa (useHintAt P h r g2 out) s fun s' => PPostB S s s' [(out, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      NatPolyIs s'.mem (pa s out) (Vector.zipWith (fun hj rj => (useHint g2 hj rj).toNat)
        ((hintAt s.mem (pa s h) 1).headD (Vector.replicate n false)) (polyAt s.mem (pa s r))) := by
  have hc' := hc
  simp only [useHintChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, c3, c4, c5, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (useHint_args L.ok g2 c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => useHint_pre L hc hg hr h1) (useHint_cov L hc).1 (useHint_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [useHintContract, useHintSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [imm32 (gamma2_lt hg)] at hq
  exact hq

theorem useHintAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.useHint (useHintContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {h r out : Ptr} (hc : useHintChk rbs wbs h r out = true)
    {g2 : Nat} (hg : g2 ∈ gamma2s) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r) ∧
      SameB x y) :
    RelCT isa Q (useHintAt P h r g2 out) fun _ _ => True := by
  have hc' := hc
  simp only [useHintChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, c3, c4, c5, _⟩ := hc'
  have hb : h.1 ∈ bases ∧ r.1 ∈ bases ∧ out.1 ∈ bases := ⟨ptr_bs hB c3, ptr_bs hB c4, ptr_bs hB c5⟩
  refine callAt_tr C (useHint_args hB g2 c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, useHint_pre Lx hc hg rx h1, ?_, ?_, (useHint_cov Lx hc).1, (useHint_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact useHint_pre Ly hc hg ry h2
  · sig_pub [useHintContract, useHintSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, trivial, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (useHint_cov Ly hc).1
  · rw [e.pa hb.2.2]; exact (useHint_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.KeyGen
