import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CallMore

/-!
# ML-DSA signing on AArch64: calls of the samplers

For each call of `vg_mldsa_rej_ntt_poly4` and `vg_mldsa_sample_in_ball`: what it
needs of the layout (`…Chk`), what it does (`…_ok`), and that two runs whose
layout registers agree, and whose sampler leaks the same, leak the same
(`…_tr`).
-/

/-! Calls of the four-way sampler through the shared contract, including public return values. -/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `RejNTTPoly` -/

def rej4Chk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB (rbs ++ wbs) seed 136 a 4096 && sepB (rbs ++ wbs) seed 136 ss 8192 && sepB (rbs ++ wbs) a 4096 ss 8192 &&
    inB (rbs ++ wbs) seed 136 && inB (rbs ++ wbs) a 4096 && inB (rbs ++ wbs) ss 8192 && inB wbs a 4096 &&
    inB wbs ss 8192

abbrev rej4Args (seed a ss : Ptr) : List (Reg × Arg) := [(.x0, .ptr seed), (.x1, .ptr a), (.x2, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : rej4Chk rbs wbs seed a ss = true)
include L hc

theorem rej4_cov : Covers ([⟨pa s seed, 136⟩] ++ [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩] s.wr := by
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨covers_append (L.cR c4) (covers_wr (covers_cons (L.cW c7) (L.cW c8))), covers_cons (L.cW c7) (L.cW c8)⟩

theorem rej4_pre {s1 : State} (h1 : Args (rej4Args seed a ss) s s1) :
    (rejNTT4Contract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 136⟩] [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩]) := by
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem rej4_args {bs : List (Reg × Nat)} (L : LayOk bs) {seed a ss : Ptr} (c4 : inB bs seed 136 = true)
    (c5 : inB bs a 4096 = true) (c6 : inB bs ss 8192 = true) :
    ∀ x ∈ rej4Args seed a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c4), by decide⟩, ⟨ptr_ok (ptr_bs L c5), by decide⟩, ⟨ptr_ok (ptr_bs L c6), by decide⟩⟩

theorem rej4AtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : rej4Chk rbs wbs seed a ss = true) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly4" ++ P.suffix) P.rej4 (rej4Args seed a ss)) s fun s' => PPostB S s s' [(a, 4096), (ss, 8192)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → ∀ k < 4,Reduced s'.mem (poly4 (pa s a) k)) ∧
      (((s'.gpr .x0).setWidth 32 = 1 ∧ ∀ k < 4,∃ b : Bounds,rejNTTPoly b.rejNTT
          (seed4 s.mem (pa s seed) k) = some (polyAt s'.mem (poly4 (pa s a) k))) ∨
        ((s'.gpr .x0).setWidth 32 = 0 ∧ ∃ k < 4,rejNTTPoly minBounds.rejNTT
          (seed4 s.mem (pa s seed) k) = none)) := by
  have hc' := hc
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAtK_ok hS C (rej4_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => rej4_pre L hc h1) (rej4_cov L hc).1 (rej4_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem rej4AtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rej4Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 136 = bytesAt y.mem (pa y seed) 136 ∧ SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_rej_ntt_poly4" ++ P.suffix) P.rej4 (rej4Args seed a ss)) fun _ _ => True := by
  have hc' := hc
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAtK_tr C (rej4_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rej4_pre Lx hc h1, ?_, ?_, (rej4_cov Lx hc).1, (rej4_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rej4_pre Ly hc h2
  · sig_pub [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rej4_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rej4_cov Ly hc).2


theorem rej4AtK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    (hr : RetPub (rejNTT4Contract AArch64.abi S) P.rej4)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rej4Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 136 = bytesAt y.mem (pa y seed) 136 ∧ SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_rej_ntt_poly4" ++ P.suffix) P.rej4 (rej4Args seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAtK_trRet C hr (rej4_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rej4_pre Lx hc h1, ?_, ?_, (rej4_cov Lx hc).1, (rej4_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rej4_pre Ly hc h2
  · sig_pub [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rej4_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rej4_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign
