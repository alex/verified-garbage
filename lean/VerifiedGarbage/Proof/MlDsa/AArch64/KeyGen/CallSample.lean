import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Base
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample

/-!
# ML-DSA key generation on AArch64: calls of `RejBoundedPoly`

For each call of `vg_mldsa_rej_bounded_poly` (the other samplers are in
`Proof/MlDsa/AArch64/Call/Sample.lean`): what it needs of the layout
(`rejBChk`), what it does (`rejBAt_ok`), and that two runs whose layout
registers agree, and whose sampler leaks the same, leak the same (`rejBAt_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def rejBChk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB rbs wbs seed 66 a 1024 && sepB rbs wbs seed 66 ss 2048 && sepB rbs wbs a 1024 ss 2048 &&
    inB (rbs ++ wbs) seed 66 && inB (rbs ++ wbs) a 1024 && inB (rbs ++ wbs) ss 2048 && inB wbs a 1024 &&
    inB wbs ss 2048

abbrev rejBArgs (seed : Ptr) (eta : Nat) (a ss : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr seed), (.x1, .imm eta), (.x2, .ptr a), (.x3, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : rejBChk rbs wbs seed a ss = true)
include L hc

theorem rejB_cov : Covers ([⟨pa s seed, 66⟩] ++ [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩] s.wr := by
  simp only [rejBChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨covers_append (L.cR c4) (covers_wr (covers_cons (L.cW c7) (L.cW c8))), covers_cons (L.cW c7) (L.cW c8)⟩

theorem rejB_pre {eta : Nat} (he : eta = 2 ∨ eta = 4) {s1 : State} (h1 : Args (rejBArgs seed eta a ss) s s1) :
    (rejBoundedContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 66⟩] [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) := by
  simp only [rejBChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejBoundedContract, rejBoundedSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1]
  simp only [Arg.val]
  rw [imm32 (by omega)]
  cpre L
  exact he

end

theorem rejB_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {seed a ss : Ptr} (eta : Nat) (c4 : inB bs seed 66 = true)
    (c5 : inB bs a 1024 = true) (c6 : inB bs ss 2048 = true) :
    ∀ x ∈ rejBArgs seed eta a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨trivial, by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩,
    ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

theorem rejBAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.rejBounded (rejBoundedContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : rejBChk rbs wbs seed a ss = true) {eta : Nat} (he : eta = 2 ∨ eta = 4) :
    WP isa (rejBoundedAt P ss seed eta a) s fun s' => PPostB S s s' [(a, 1024), (ss, 2048)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => (rejBoundedPoly eta b.rejBounded (bytesAt s.mem (pa s seed) 66)).map toRq)
        ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (pa s a)) := by
  have hc' := hc
  simp only [rejBChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (rejB_args L.ok eta c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => rejB_pre L hc he h1) (rejB_cov L hc).1 (rejB_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejBoundedContract, rejBoundedSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [imm32 (by omega)] at hq
  exact hq

theorem rejBAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.rejBounded (rejBoundedContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rejBChk rbs wbs seed a ss = true)
    {eta : Nat} (he : eta = 2 ∨ eta = 4) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      rejBoundedLeak eta (bytesAt x.mem (pa x seed) 66) = rejBoundedLeak eta (bytesAt y.mem (pa y seed) 66) ∧
      SameB x y) :
    RelCT isa Q (rejBoundedAt P ss seed eta a) fun _ _ => True := by
  have hc' := hc
  simp only [rejBChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (rejB_args hB eta c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rejB_pre Lx hc he h1, ?_, ?_, (rejB_cov Lx hc).1, (rejB_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rejB_pre Ly hc he h2
  · sig_pub [rejBoundedContract, rejBoundedSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    rw [imm32 (by omega)]
    exact ⟨e.2, hsd, e.pa hb.1, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rejB_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rejB_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.KeyGen
