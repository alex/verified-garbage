import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallRound

/-!
# ML-DSA on AArch64: calls of the encodings

Untrusted: everything here is checked by Lean. For each call of
`vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack`,
`vg_mldsa_unpack_t1` and `vg_mldsa_hint_bit_unpack`: what it needs of the
layout (`…Chk`), what it does (`…_ok`), and that two runs whose layout
registers agree (and whose hint agrees) leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A polynomial read and a buffer written, apart. -/
def rwChk (rbs wbs : List (Reg × Nat)) (f : Ptr) (lf : Nat) (out : Ptr) (lo : Nat) : Bool :=
  sepB rbs wbs f lf out lo && inB (rbs ++ wbs) f lf && inB (rbs ++ wbs) out lo && inB wbs out lo

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f out : Ptr} {lf lo : Nat}
  (hc : rwChk rbs wbs f lf out lo = true)
include L hc

theorem rw_cov : Covers ([⟨pa s f, lf⟩] ++ [⟨pa s out, lo⟩]) (s.rd ++ s.wr) ∧ Covers [⟨pa s out, lo⟩] s.wr := by
  simp only [rwChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, c2, _, c4⟩ := hc
  exact ⟨covers_append (L.cR c2) (covers_wr (L.cW c4)), L.cW c4⟩

end

theorem rw_parts {rbs wbs : List (Reg × Nat)} {f out : Ptr} {lf lo : Nat} (hc : rwChk rbs wbs f lf out lo = true) :
    sepB rbs wbs f lf out lo = true ∧ inB (rbs ++ wbs) f lf = true ∧ inB (rbs ++ wbs) out lo = true := by
  simp only [rwChk, Bool.and_eq_true, and_assoc] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2.1⟩

/-! ## `SimpleBitPack` -/

abbrev sbpArgs (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.x0, .ptr f), (.x1, .imm b), (.x2, .ptr out), (.x3, .imm len)]

theorem sbp_args {bs : List (Reg × Nat)} (L : LayOk bs) {f out : Ptr} (b len : Nat) (c2 : inB bs f 1024 = true)
    (c3 : inB bs out len = true) : ∀ x ∈ sbpArgs f b out len, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨ptr_ok (ptr_bs L c3), by decide⟩,
    ⟨trivial, by decide⟩⟩

/-- What `SimpleBitPack` asks of its arguments. -/
structure SbpOk (b len : Nat) : Prop where
  hb : b ∈ simpleBitPackBounds
  hlen : len = 32 * bitlen b
  hlt : b < 2 ^ 32 ∧ len < 2 ^ 32

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f out : Ptr} {b len : Nat}
  (hc : rwChk rbs wbs f 1024 out len = true)
include L hc

theorem sbp_pre (hb : SbpOk b len) (hf : ∀ i < n, (coeffAt s.mem (pa s f) i).toNat ≤ b) {s1 : State}
    (h1 : Args (sbpArgs f b out len) s s1) :
    (simpleBitPackContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨pa s f, 1024⟩] [⟨pa s out, len⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  sig_pre [simpleBitPackContract, simpleBitPackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, imm32 hb.hlt.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2; omega)]
  cpre L
  exacts [hb.hb, hb.hlen, hf]

end

theorem sbpAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.simpleBitPack (simpleBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f out : Ptr} {b len : Nat}
    (hc : rwChk rbs wbs f 1024 out len = true) (hb : SbpOk b len)
    (hf : ∀ i < n, (coeffAt s.mem (pa s f) i).toNat ≤ b) :
    WP isa (simpleBitPackAt P f b out len) s fun s' => PPostB S s s' [(out, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s out) len = simpleBitPack (natPolyAt s.mem (pa s f)) b := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  refine WP.mono (callAt_ok hS C (sbp_args L.ok b len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => sbp_pre L hc hb hf h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [simpleBitPackContract, simpleBitPackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 hb.hlt.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2; omega)] at hq
  exact hq

theorem sbpAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.simpleBitPack (simpleBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {f out : Ptr} {b len : Nat}
    (hc : rwChk rbs wbs f 1024 out len = true) (hb : SbpOk b len) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ (∀ i < n, (coeffAt x.mem (pa x f) i).toNat ≤ b) ∧
      (∀ i < n, (coeffAt y.mem (pa y f) i).toNat ≤ b) ∧ SameB x y) :
    RelCT isa Q (simpleBitPackAt P f b out len) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hbs : f.1 ∈ bases ∧ out.1 ∈ bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (sbp_args hB b len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, sbp_pre Lx hc hb rx h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact sbp_pre Ly hc hb ry h2
  · sig_pub [simpleBitPackContract, simpleBitPackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hbs.1, trivial, e.pa hbs.2, trivial⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Ly hc).2

/-! ## `BitPack` -/

abbrev bpArgs (f : Ptr) (a b : Nat) (out : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.x0, .ptr f), (.x1, .imm a), (.x2, .imm b), (.x3, .ptr out), (.x4, .imm len)]

theorem bp_args {bs : List (Reg × Nat)} (L : LayOk bs) {f out : Ptr} (a b len : Nat) (c2 : inB bs f 1024 = true)
    (c3 : inB bs out len = true) : ∀ x ∈ bpArgs f a b out len, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_bs L c3), by decide⟩, ⟨trivial, by decide⟩⟩

/-- What `BitPack` and `BitUnpack` ask of their arguments. -/
structure BpOk (a b len : Nat) : Prop where
  hab : (a, b) ∈ bitPackParams
  hlen : len = 32 * bitlen (a + b)
  hlt : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ len < 2 ^ 32

/-- The coefficients `BitPack` packs are in range. -/
def BpRange (m : Mem) (f : Addr) (a b : Nat) : Prop :=
  ∀ i < n, -(a : Int) ≤ modPm (coeffAt m f i).toNat q ∧ modPm (coeffAt m f i).toNat q ≤ b

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f out : Ptr} {a b len : Nat}
  (hc : rwChk rbs wbs f 1024 out len = true)
include L hc

theorem bp_pre (hb : BpOk a b len) (hr : Reduced s.mem (pa s f)) (hf : BpRange s.mem (pa s f) a b) {s1 : State}
    (h1 : Args (bpArgs f a b out len) s s1) :
    (bitPackContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨pa s f, 1024⟩] [⟨pa s out, len⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  sig_pre [bitPackContract, bitPackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, imm32 hb.hlt.1, imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2.2; omega)]
  cpre L
  exacts [hb.hab, hb.hlen, hr, hf]

end

theorem bpAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.bitPack (bitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f out : Ptr} {a b len : Nat}
    (hc : rwChk rbs wbs f 1024 out len = true) (hb : BpOk a b len) (hr : Reduced s.mem (pa s f))
    (hf : BpRange s.mem (pa s f) a b) :
    WP isa (bitPackAt P f a b out len) s fun s' => PPostB S s s' [(out, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s out) len = bitPack ((polyAt s.mem (pa s f)).map fun c => modPm c.val q) a b := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  refine WP.mono (callAt_ok hS C (bp_args L.ok a b len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => bp_pre L hc hb hr hf h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [bitPackContract, bitPackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 hb.hlt.1, imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2.2; omega)] at hq
  exact hq

theorem bpAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.bitPack (bitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {f out : Ptr} {a b len : Nat}
    (hc : rwChk rbs wbs f 1024 out len = true) (hb : BpOk a b len) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      (Reduced x.mem (pa x f) ∧ BpRange x.mem (pa x f) a b) ∧ (Reduced y.mem (pa y f) ∧ BpRange y.mem (pa y f) a b) ∧
      SameB x y) :
    RelCT isa Q (bitPackAt P f a b out len) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hbs : f.1 ∈ bases ∧ out.1 ∈ bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (bp_args hB a b len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, bp_pre Lx hc hb rx.1 rx.2 h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact bp_pre Ly hc hb ry.1 ry.2 h2
  · sig_pub [bitPackContract, bitPackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hbs.1, trivial, trivial, e.pa hbs.2, trivial⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Ly hc).2

/-! ## `BitUnpack` -/

abbrev buArgs (v : Ptr) (len a b : Nat) (f : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr v), (.x1, .imm len), (.x2, .imm a), (.x3, .imm b), (.x4, .ptr f)]

theorem bu_args {bs : List (Reg × Nat)} (L : LayOk bs) {v f : Ptr} (len a b : Nat) (c2 : inB bs v len = true)
    (c3 : inB bs f 1024 = true) : ∀ x ∈ buArgs v len a b f, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_bs L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {v f : Ptr} {a b len : Nat}
  (hc : rwChk rbs wbs v len f 1024 = true)
include L hc

theorem bu_pre (hb : BpOk a b len) {s1 : State} (h1 : Args (buArgs v len a b f) s s1) :
    (bitUnpackContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨pa s v, len⟩] [⟨pa s f, 1024⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  sig_pre [bitUnpackContract, bitUnpackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1]
  simp only [Arg.val, imm32 hb.hlt.1, imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2.2; omega)]
  cpre L
  exacts [hb.hab, hb.hlen]

end

theorem buAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.bitUnpack (bitUnpackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {v f : Ptr} {a b len : Nat}
    (hc : rwChk rbs wbs v len f 1024 = true) (hb : BpOk a b len) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => PPostB S s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s f) (toRq (bitUnpack (bytesAt s.mem (pa s v) len) a b)) := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  refine WP.mono (callAt_ok hS C (bu_args L.ok len a b c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => bu_pre L hc hb h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [bitUnpackContract, bitUnpackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 hb.hlt.1, imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.2.2; omega)] at hq
  exact hq

theorem buAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.bitUnpack (bitUnpackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {v f : Ptr} {a b len : Nat}
    (hc : rwChk rbs wbs v len f 1024 = true) (hb : BpOk a b len) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ SameB x y) :
    RelCT isa Q (bitUnpackAt P v len a b f) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hbs : v.1 ∈ bases ∧ f.1 ∈ bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (bu_args hB len a b c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, bu_pre Lx hc hb h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact bu_pre Ly hc hb h2
  · sig_pub [bitUnpackContract, bitUnpackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hbs.1, trivial, trivial, trivial, e.pa hbs.2⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Ly hc).2

/-! ## `t₁` -/

abbrev t1Args (v f : Ptr) : List (Reg × Arg) := [(.x0, .ptr v), (.x1, .ptr f)]

theorem t1_args {bs : List (Reg × Nat)} (L : LayOk bs) {v f : Ptr} (c2 : inB bs v 320 = true)
    (c3 : inB bs f 1024 = true) : ∀ x ∈ t1Args v f, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c2), by decide⟩, ⟨ptr_ok (ptr_bs L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {v f : Ptr}
  (hc : rwChk rbs wbs v 320 f 1024 = true)
include L hc

theorem t1_pre {s1 : State} (h1 : Args (t1Args v f) s s1) :
    (unpackT1Contract AArch64.abi S).pre (s1.callEntry.withRegions [⟨pa s v, 320⟩] [⟨pa s f, 1024⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  sig_pre [unpackT1Contract, unpackT1Sig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem t1At_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.unpackT1 (unpackT1Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {v f : Ptr}
    (hc : rwChk rbs wbs v 320 f 1024 = true) :
    WP isa (unpackT1At P v f) s fun s' => PPostB S s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s f) ((simpleBitUnpack (bytesAt s.mem (pa s v) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  refine WP.mono (callAt_ok hS C (t1_args L.ok c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => t1_pre L hc h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [unpackT1Contract, unpackT1Sig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem t1At_tr {S : Nat} {P : Prims} (C : CalleeOk S P.unpackT1 (unpackT1Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {v f : Ptr}
    (hc : rwChk rbs wbs v 320 f 1024 = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ SameB x y) :
    RelCT isa Q (unpackT1At P v f) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hbs : v.1 ∈ bases ∧ f.1 ∈ bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (t1_args hB c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, t1_pre Lx hc h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact t1_pre Ly hc h2
  · sig_pub [unpackT1Contract, unpackT1Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r0 h2, Args.r1 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hbs.1, e.pa hbs.2⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Ly hc).2

/-! ## `HintBitUnpack` -/

abbrev huArgs (y : Ptr) (len omega : Nat) (h : Ptr) (hlen : Nat) : List (Reg × Arg) :=
  [(.x0, .ptr y), (.x1, .imm len), (.x2, .imm omega), (.x3, .ptr h), (.x4, .imm hlen)]

theorem hu_args {bs : List (Reg × Nat)} (L : LayOk bs) {y h : Ptr} (len omega hlen : Nat) (c2 : inB bs y len = true)
    (c3 : inB bs h (hlen * 4) = true) : ∀ x ∈ huArgs y len omega h hlen, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_bs L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_bs L c3), by decide⟩, ⟨trivial, by decide⟩⟩

/-- What `HintBitUnpack` asks of its arguments. -/
structure HuOk (len omega hlen : Nat) : Prop where
  hp : (omega, len - omega) ∈ hintParams
  hle : omega ≤ len
  hhl : hlen = 256 * (len - omega)
  hlt : len < 2 ^ 32 ∧ omega < 2 ^ 32 ∧ hlen < 2 ^ 32

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {y h : Ptr} {len omega hlen : Nat}
  (hc : rwChk rbs wbs y len h (hlen * 4) = true)
include L hc

theorem hu_pre (hb : HuOk len omega hlen) {s1 : State} (h1 : Args (huArgs y len omega h hlen) s s1) :
    (hintBitUnpackContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s y, len⟩] [⟨pa s h, hlen * 4⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1]
  simp only [Arg.val, imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.1; omega),
    Nat.mod_eq_of_lt (show hlen < 2 ^ 64 by have := hb.hlt.2.2; omega)]
  cpre L
  exacts [hb.hp, hb.hle, hb.hhl]

end

theorem huAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.hintUnpack (hintBitUnpackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {y h : Ptr} {len omega hlen : Nat}
    (hc : rwChk rbs wbs y len h (hlen * 4) = true) (hb : HuOk len omega hlen) :
    WP isa (hintUnpackAt P y len omega h hlen) s fun s' => PPostB S s s' [(h, hlen * 4)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      match hintBitUnpack omega (len - omega) (bytesAt s.mem (pa s y) len) with
      | some hint => (s'.gpr .x0).setWidth 32 = 1 ∧ HintIs s'.mem (pa s h) (len - omega) hint
      | none => (s'.gpr .x0).setWidth 32 = 0 := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  refine WP.mono (callAt_ok hS C (hu_args L.ok len omega hlen c2 c3)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => hu_pre L hc hb h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [hintBitUnpackContract, hintBitUnpackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.1; omega)] at hq
  exact hq

theorem huAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.hintUnpack (hintBitUnpackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {y h : Ptr} {len omega hlen : Nat}
    (hc : rwChk rbs wbs y len h (hlen * 4) = true) (hb : HuOk len omega hlen) {Q : State → State → Prop}
    (hQ : ∀ x z, Q x z → Lay S rbs wbs x ∧ Lay S rbs wbs z ∧
      bytesAt x.mem (pa x y) len = bytesAt z.mem (pa z y) len ∧ SameB x z) :
    RelCT isa Q (hintUnpackAt P y len omega h hlen) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hbs : y.1 ∈ bases ∧ h.1 ∈ bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (hu_args hB len omega hlen c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x z x1 z1 hp h1 h2 => ?_
  obtain ⟨Lx, Lz, hy, e⟩ := hQ x z hp
  refine ⟨_, _, hu_pre Lx hc hb h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact hu_pre Lz hc hb h2
  · sig_pub [hintBitUnpackContract, hintBitUnpackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.1; omega)]
    exact ⟨e.2, by rw [hy], e.pa hbs.1, trivial, trivial, e.pa hbs.2, trivial⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Lz hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Lz hc).2

end VG.Proof.MlDsa.AArch64.KeyGen
