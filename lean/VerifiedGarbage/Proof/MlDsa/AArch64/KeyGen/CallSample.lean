import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallArith

/-!
# ML-DSA on AArch64: calls of the samplers

Untrusted: everything here is checked by Lean. For each call of
`vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly` and
`vg_mldsa_sample_in_ball`: what it needs of the layout (`…Chk`), what it
does (`…_ok`), and that two runs whose layout registers agree, and whose
sampler leaks the same, leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `RejNTTPoly` -/

def rejNttChk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB rbs wbs seed 34 a 1024 && sepB rbs wbs seed 34 ss 2048 && sepB rbs wbs a 1024 ss 2048 &&
    inB (rbs ++ wbs) seed 34 && inB (rbs ++ wbs) a 1024 && inB (rbs ++ wbs) ss 2048 && inB wbs a 1024 &&
    inB wbs ss 2048

abbrev rejNttArgs (seed a ss : Ptr) : List (Reg × Arg) := [(.x0, .ptr seed), (.x1, .ptr a), (.x2, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : rejNttChk rbs wbs seed a ss = true)
include L hc

theorem rejNtt_cov : Covers ([⟨pa s seed, 34⟩] ++ [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩] s.wr := by
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨covers_append (L.cR c4) (covers_wr (covers_cons (L.cW c7) (L.cW c8))), covers_cons (L.cW c7) (L.cW c8)⟩

theorem rejNtt_pre {s1 : State} (h1 : Args (rejNttArgs seed a ss) s s1) :
    (rejNTTContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 34⟩] [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) := by
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem rejNtt_args {bs : List (Reg × Nat)} (L : LayOk bs) {seed a ss : Ptr} (c4 : inB bs seed 34 = true)
    (c5 : inB bs a 1024 = true) (c6 : inB bs ss 2048 = true) :
    ∀ x ∈ rejNttArgs seed a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c4), by decide⟩, ⟨ptr_ok (ptr_bs L c5), by decide⟩, ⟨ptr_ok (ptr_bs L c6), by decide⟩⟩

theorem rejNttAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.rejNtt (rejNTTContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : rejNttChk rbs wbs seed a ss = true) :
    WP isa (rejNttAt P ss seed a) s fun s' => PPostB S s s' [(a, 1024), (ss, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (pa s seed) 34)) ((s'.gpr .x0).setWidth 32)
        (polyAt s'.mem (pa s a)) := by
  have hc' := hc
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (rejNtt_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => rejNtt_pre L hc h1) (rejNtt_cov L hc).1 (rejNtt_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem rejNttAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.rejNtt (rejNTTContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rejNttChk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 34 = bytesAt y.mem (pa y seed) 34 ∧ SameB x y) :
    RelCT isa Q (rejNttAt P ss seed a) fun _ _ => True := by
  have hc' := hc
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (rejNtt_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rejNtt_pre Lx hc h1, ?_, ?_, (rejNtt_cov Lx hc).1, (rejNtt_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rejNtt_pre Ly hc h2
  · sig_pub [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rejNtt_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rejNtt_cov Ly hc).2

/-! ## `RejBoundedPoly` -/

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

theorem rejB_args {bs : List (Reg × Nat)} (L : LayOk bs) {seed a ss : Ptr} (eta : Nat) (c4 : inB bs seed 66 = true)
    (c5 : inB bs a 1024 = true) (c6 : inB bs ss 2048 = true) :
    ∀ x ∈ rejBArgs seed eta a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c4), by decide⟩, ⟨trivial, by decide⟩, ⟨ptr_ok (ptr_bs L c5), by decide⟩,
    ⟨ptr_ok (ptr_bs L c6), by decide⟩⟩

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

/-! ## `SampleInBall` -/

def ballChk (rbs wbs : List (Reg × Nat)) (ct : Ptr) (len : Nat) (c ss : Ptr) : Bool :=
  sepB rbs wbs ct len c 1024 && sepB rbs wbs ct len ss 2048 && sepB rbs wbs c 1024 ss 2048 &&
    inB (rbs ++ wbs) ct len && inB (rbs ++ wbs) c 1024 && inB (rbs ++ wbs) ss 2048 && inB wbs c 1024 &&
    inB wbs ss 2048

abbrev ballArgs (ct : Ptr) (len tau : Nat) (c ss : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr ct), (.x1, .imm len), (.x2, .imm tau), (.x3, .ptr c), (.x4, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {ct c ss : Ptr} {len : Nat}
  (hc : ballChk rbs wbs ct len c ss = true)
include L hc

theorem ball_cov : Covers ([⟨pa s ct, len⟩] ++ [⟨pa s c, 1024⟩, ⟨pa s ss, 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s c, 1024⟩, ⟨pa s ss, 2048⟩] s.wr := by
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨covers_append (L.cR c4) (covers_wr (covers_cons (L.cW c7) (L.cW c8))), covers_cons (L.cW c7) (L.cW c8)⟩

theorem ball_pre {tau : Nat} (ht : (len, tau) ∈ ballParams) {s1 : State}
    (h1 : Args (ballArgs ct len tau c ss) s s1) :
    (sampleInBallContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s ct, len⟩] [⟨pa s c, 1024⟩, ⟨pa s ss, 2048⟩]) := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ht; omega
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1]
  simp only [Arg.val]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), imm32 hl.2]
  cpre L
  exact ht

end

theorem ball_args {bs : List (Reg × Nat)} (L : LayOk bs) {ct c ss : Ptr} (len tau : Nat) (c4 : inB bs ct len = true)
    (c5 : inB bs c 1024 = true) (c6 : inB bs ss 2048 = true) :
    ∀ x ∈ ballArgs ct len tau c ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c4), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_bs L c5), by decide⟩, ⟨ptr_ok (ptr_bs L c6), by decide⟩⟩

theorem ballAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.ball (sampleInBallContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {ct c ss : Ptr} {len : Nat}
    (hc : ballChk rbs wbs ct len c ss = true) {tau : Nat} (ht : (len, tau) ∈ ballParams) :
    WP isa (ballAt P ss ct len tau c) s fun s' => PPostB S s s' [(c, 1024), (ss, 2048)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (pa s ct) len)).map toRq)
        ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (pa s c)) := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ht; omega
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (ball_args L.ok len tau c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => ball_pre L hc ht h1) (ball_cov L hc).1 (ball_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), imm32 hl.2] at hq
  exact hq

theorem ballAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.ball (sampleInBallContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {ct c ss : Ptr} {len : Nat}
    (hc : ballChk rbs wbs ct len c ss = true) {tau : Nat} (ht : (len, tau) ∈ ballParams) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x ct) len = bytesAt y.mem (pa y ct) len ∧ SameB x y) :
    RelCT isa Q (ballAt P ss ct len tau c) fun _ _ => True := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ht; omega
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : ct.1 ∈ bases ∧ c.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (ball_args hB len tau c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, ball_pre Lx hc ht h1, ?_, ?_, (ball_cov Lx hc).1, (ball_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact ball_pre Ly hc ht h2
  · sig_pub [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, trivial, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (ball_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (ball_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.KeyGen
