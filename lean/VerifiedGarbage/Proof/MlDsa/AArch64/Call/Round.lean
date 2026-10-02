import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry

/-!
# ML-DSA on AArch64: calls of the norm

For each call of `vg_mldsa_norm_lt`: what it needs of the layout (`…Chk`),
what it does (`…_ok`), and that two runs whose layout registers agree leak the
same (`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64 VG.Impl.MlDsa.AArch64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The norm -/

abbrev normArgs (f : Ptr) (bound : Nat) : List (Reg × Arg) := [(.x0, .ptr f), (.x1, .imm bound)]

theorem norm_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {f : Ptr} (bound : Nat) (c1 : inB bs f 1024 = true) :
    ∀ x ∈ normArgs f bound, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c1), by decide⟩, ⟨trivial, by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f : Ptr}
  (hc : inB (rbs ++ wbs) f 1024 = true)
include L hc

theorem norm_cov : Covers ([⟨pa s f, 1024⟩] ++ []) (s.rd ++ s.wr) ∧ Covers [] s.wr :=
  ⟨by rw [List.append_nil]; exact L.cR hc, covers_nil⟩

theorem norm_pre {bound : Nat} (hr : Reduced s.mem (pa s f)) {s1 : State} (h1 : Args (normArgs f bound) s s1) :
    (normLtContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨pa s f, 1024⟩] []) := by
  sig_pre [normLtContract, normLtSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exact hr

end

theorem normAt_ok {S : Nat} (hS : S < 2 ^ 64) {nm : String} {cd : Prog isa} (C : CalleeOk S cd (normLtContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f : Ptr} (hc : inB (rbs ++ wbs) f 1024 = true)
    {bound : Nat} (hb : bound < 2 ^ 32) (hr : Reduced s.mem (pa s f)) :
    WP isa (callAt nm cd (normArgs f bound)) s fun s' => PPostB S s s' [] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      (s'.gpr .x0).setWidth 32 = if normRq [polyAt s.mem (pa s f)] < bound then 1 else 0 := by
  refine WP.mono (callAt_ok hS C (norm_args L.ok bound hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => norm_pre L hc hr h1) (norm_cov L hc).1 (norm_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [normLtContract, normLtSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 hb] at hq
  exact hq

theorem normAt_tr {S : Nat} {nm : String} {cd : Prog isa} (C : CalleeOk S cd (normLtContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : LayIn B (rbs ++ wbs)) {f : Ptr} (hc : inB (rbs ++ wbs) f 1024 = true)
    {bound : Nat} {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f) ∧
      SameIn B x y) :
    RelCT isa Q (callAt nm cd (normArgs f bound)) fun _ _ => True := by
  have hb : f.1 ∈ B := ptr_bs hB hc
  refine callAt_tr C (norm_args hB bound hc) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, norm_pre Lx hc rx h1, ?_, ?_, (norm_cov Lx hc).1, (norm_cov Lx hc).2, ?_, (norm_cov Ly hc).2⟩
  · rw [e.pa hb]; exact norm_pre Ly hc ry h2
  · sig_pub [normLtContract, normLtSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r0 h2, Args.r1 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb, trivial⟩
  · rw [e.pa hb]; exact (norm_cov Ly hc).1

/-- The values of `γ₂`, as an immediate. -/
theorem gamma2_lt {g2 : Nat} (h : g2 ∈ gamma2s) : g2 < 2 ^ 32 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64
