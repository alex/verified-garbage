import VerifiedGarbage.Impl.MlKem1024.X86_64.Frag
import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.KPke1024

/-!
# ML-KEM-1024 on x86-64: the pieces of the top-level functions

Untrusted: everything here is checked by Lean. As `FragPrim.lean`,
`FragL.lean`, `FragS.lean` and `FragC.lean` of ML-KEM-768 (whose lemmas
the others are), for the pieces ML-KEM-1024 adds: the calls of
`vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`
(`ce4At_ok`, `dd4At_ok`, …, and in a layout `ce4At_okL`, …), an entry of
`Â` at any polynomial (`sampP_ok`, `sampP_tr`), and sums of four products
(`dot4At_ok`, `dot4At_tr`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem ce4_nosp : NoSp compressEncode1024 := nosp_of (by decide +kernel)
theorem dd4_nosp : NoSp decodeDecompress1024 := nosp_of (by decide +kernel)
theorem ce4_depth : compressEncode1024.depth = 0 := by decide +kernel
theorem dd4_depth : decodeDecompress1024.depth = 0 := by decide +kernel

theorem widths4_lt {d : Nat} (h : d ∈ Spec.MlKem1024.compressWidths) : d ≤ 11 := by
  rcases widths1024 h with rfl | rfl <;> decide

/-! ## `ByteEncode_d ∘ Compress_d` -/

/-- What a call of `vg_mlkem1024_compress_encode` of `f` to `out` with width `d` needs. -/
structure CEH4 (f out : Ptr) (d : Nat) (s : State) : Prop where
  off : f.2 < 2 ^ 31 ∧ out.2 < 2 ^ 31
  dw : d ∈ Spec.MlKem1024.compressWidths
  red : Reduced s.mem (pa s f)
  dj : Region.Disjoint (pR (pa s f)) ⟨pa s out, 32 * d⟩
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (pa s f))
  kO : (below (s.gpr .rsp) 32).Disjoint ⟨pa s out, 32 * d⟩
  c : Covers ([pR (pa s f)] ++ [⟨pa s out, 32 * d⟩]) (s.rd ++ s.wr)
  w : Covers [⟨pa s out, 32 * d⟩] s.wr

theorem ce4Glue_ok (f out : Ptr) (d : Nat) (ho : f.2 < 2 ^ 31 ∧ out.2 < 2 ^ 31) (hd : d ≤ 11) (hout : NA out)
    (s : State) :
    WP isa (.block (lea .rdi f ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 d))] : List Instr) ++ lea .rdx out ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) s fun s1 =>
      ((s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 d ∧ s1.gpr .rdx = pa s out ∧
        s1.gpr .rcx = BitVec.ofNat 64 (32 * d)) ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 := by
  have o1 : out.1 ≠ .rsi := fun e => hout (by rw [e]; decide)
  have o2 : out.1 ≠ .rdi := fun e => hout (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2, o1, o2, sw_ofNat (show d < 2 ^ 32 by omega),
    sw_ofNat (show 32 * d < 2 ^ 32 by omega), List.cons_append, List.nil_append]

theorem ce4Pre {f out : Ptr} {d : Nat} {s s1 : State} (h : CEH4 f out d s)
    (hv : s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 d ∧ s1.gpr .rdx = pa s out ∧
      s1.gpr .rcx = BitVec.ofNat 64 (32 * d)) (hm : s1.mem = s.mem) (k : Keep MlKem.X86_64.argRegs s s1) :
    compressEncode1024K.pre (s1.callEntry.withRegions [pR (pa s f)] [⟨pa s out, 32 * d⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hd := widths4_lt h.dw
  simp only [compressEncode1024K, dArg, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2,
    ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega)]
  refine ⟨trivial, trivial, h.dj, ret_disj s1 (by rw [hsp]; exact h.kF), ret_disj s1 (by rw [hsp]; exact h.kO),
    h.dw, trivial, ?_⟩
  rw [ce_reduced s1 (by rw [hsp]; exact h.kF), hm]; exact h.red

theorem ce4At_ok {f out : Ptr} {d : Nat} (hout : NA out) {s : State} (h : CEH4 f out d s) :
    WP isa (ce4At f d out) s fun s' => Post s s' [⟨pa s out, 32 * d⟩] ∧
      bytesAt s'.mem (pa s out) (32 * d) = compressEncode d (polyAt s.mem (pa s f)) := by
  have hd := widths4_lt h.dw
  refine WP.mono (glueCall_ok compressEncode1024_correct ce4_nosp (by rw [ce4_depth]; decide)
    (ce4Glue_ok f out d h.off hd hout s) (fun s1 hv hm k => ce4Pre h hv hm k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [compressEncode1024K, dArg, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, hm₂, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega),
    ce_polyAt s1 (by rw [hsp]; exact h.kF), hm] at hq
  exact hq

theorem ce4At_tr {f out : Ptr} {d : Nat} (hout : NA out) :
    RelCT isa (fun x y => CEH4 f out d x ∧ CEH4 f out d y ∧ x.gpr f.1 = y.gpr f.1 ∧ x.gpr out.1 = y.gpr out.1 ∧
      x.gpr .rsp = y.gpr .rsp) (ce4At f d out) fun _ _ => True :=
  glueCall_tr compressEncode1024_correct compressEncode1024_ct (V := fun x x1 => ((x1.gpr .rdi = pa x f ∧
      x1.gpr .rsi = BitVec.ofNat 64 d ∧ x1.gpr .rdx = pa x out ∧ x1.gpr .rcx = BitVec.ofNat 64 (32 * d)) ∧
      x1.mem = x.mem) ∧ Keep MlKem.X86_64.argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (mov32i_nomem _ _)) (lea_nomem _ _))
      (mov32i_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨ce4Glue_ok f out d hx.off (widths4_lt hx.dw) hout x,
      ce4Glue_ok f out d hy.off (widths4_lt hy.dw) hout y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, ce4Pre hx hv1 hm1 k1, ce4Pre hy hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [compressEncode1024K, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]

/-! ## `Decompress_d ∘ ByteDecode_d` -/

/-- What a call of `vg_mlkem1024_decode_decompress` of the `32d` bytes at `b` to `f` needs. -/
structure DDH4 (b f : Ptr) (d : Nat) (s : State) : Prop where
  off : b.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31
  dw : d ∈ Spec.MlKem1024.compressWidths
  dj : Region.Disjoint ⟨pa s b, 32 * d⟩ (pR (pa s f))
  kB : (below (s.gpr .rsp) 32).Disjoint ⟨pa s b, 32 * d⟩
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (pa s f))
  c : Covers ([⟨pa s b, 32 * d⟩] ++ [pR (pa s f)]) (s.rd ++ s.wr)
  w : Covers [pR (pa s f)] s.wr

theorem dd4Glue_ok (b f : Ptr) (d : Nat) (ho : b.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31) (hd : d ≤ 11) (hf : NA f) (s : State) :
    WP isa (.block (lea .rdi b ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * d))),
      .mov32 .rdx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ lea .rcx f)) s fun s1 =>
      ((s1.gpr .rdi = pa s b ∧ s1.gpr .rsi = BitVec.ofNat 64 (32 * d) ∧ s1.gpr .rdx = BitVec.ofNat 64 d ∧
        s1.gpr .rcx = pa s f) ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 := by
  have o1 : f.1 ≠ .rsi := fun e => hf (by rw [e]; decide)
  have o2 : f.1 ≠ .rdi := fun e => hf (by rw [e]; decide)
  have o3 : f.1 ≠ .rdx := fun e => hf (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2, o1, o2, o3, sw_ofNat (show d < 2 ^ 32 by omega),
    sw_ofNat (show 32 * d < 2 ^ 32 by omega), List.cons_append, List.nil_append]

theorem dd4Pre {b f : Ptr} {d : Nat} {s s1 : State} (h : DDH4 b f d s)
    (hv : s1.gpr .rdi = pa s b ∧ s1.gpr .rsi = BitVec.ofNat 64 (32 * d) ∧ s1.gpr .rdx = BitVec.ofNat 64 d ∧
      s1.gpr .rcx = pa s f) (k : Keep MlKem.X86_64.argRegs s s1) :
    decodeDecompress1024K.pre (s1.callEntry.withRegions [⟨pa s b, 32 * d⟩] [pR (pa s f)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hd := widths4_lt h.dw
  simp only [decodeDecompress1024K, dArg, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2,
    ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega)]
  exact ⟨trivial, trivial, h.dj, ret_disj s1 (by rw [hsp]; exact h.kB), ret_disj s1 (by rw [hsp]; exact h.kF),
    h.dw, trivial⟩

theorem dd4At_ok {b f : Ptr} {d : Nat} (hf : NA f) {s : State} (h : DDH4 b f d s) :
    WP isa (dd4At b d f) s fun s' => Post s s' [pR (pa s f)] ∧
      PolyIs s'.mem (pa s f) (decodeDecompress d (bytesAt s.mem (pa s b) (32 * d))) := by
  have hd := widths4_lt h.dw
  refine WP.mono (glueCall_ok decodeDecompress1024_correct dd4_nosp (by rw [dd4_depth]; decide)
    (dd4Glue_ok b f d h.off hd hf s) (fun s1 hv _ k => dd4Pre h hv k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [decodeDecompress1024K, dArg, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, hm₂, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega),
    ce_bytesAt s1 (n := 32 * d) (by omega) (by rw [hsp]; exact h.kB), hm] at hq
  exact hq

theorem dd4At_tr {b f : Ptr} {d : Nat} (hf : NA f) :
    RelCT isa (fun x y => DDH4 b f d x ∧ DDH4 b f d y ∧ x.gpr b.1 = y.gpr b.1 ∧ x.gpr f.1 = y.gpr f.1 ∧
      x.gpr .rsp = y.gpr .rsp) (dd4At b d f) fun _ _ => True :=
  glueCall_tr decodeDecompress1024_correct decodeDecompress1024_ct (V := fun x x1 => ((x1.gpr .rdi = pa x b ∧
      x1.gpr .rsi = BitVec.ofNat 64 (32 * d) ∧ x1.gpr .rdx = BitVec.ofNat 64 d ∧ x1.gpr .rcx = pa x f) ∧
      x1.mem = x.mem) ∧ Keep MlKem.X86_64.argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (fun i hi s => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> rfl)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨dd4Glue_ok b f d hx.off (widths4_lt hx.dw) hf x,
      dd4Glue_ok b f d hy.off (widths4_lt hy.dw) hf y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, _⟩, k1⟩ ⟨⟨hv2, _⟩, k2⟩ => by
      refine ⟨_, _, _, _, dd4Pre hx hv1 k1, dd4Pre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [decodeDecompress1024K, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]

/-! ## In a layout -/

section
variable {rbs wbs : List (Reg × Nat)}

theorem CEH4.of {s : State} (L : Lay rbs wbs s) {f out : Ptr} {d : Nat}
    (hc : twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true) (hd : d ∈ Spec.MlKem1024.compressWidths)
    (red : Reduced s.mem (pa s f)) : CEH4 f out d s :=
  have h := TwoH.of L hc
  ⟨h.off, hd, red, h.d, h.kP, h.kQ, h.c, h.w⟩

theorem DDH4.of {s : State} (L : Lay rbs wbs s) {b f : Ptr} {d : Nat}
    (hc : twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true) (hd : d ∈ Spec.MlKem1024.compressWidths) : DDH4 b f d s :=
  have h := TwoH.of L hc
  ⟨h.off, hd, h.d, h.kP, h.kQ, h.c, h.w⟩

theorem ce4At_okL {s : State} (L : Lay rbs wbs s) {f out : Ptr} {d : Nat} (hout : NA out)
    (hc : twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true) (hd : d ∈ Spec.MlKem1024.compressWidths)
    (red : Reduced s.mem (pa s f)) :
    WP isa (ce4At f d out) s fun s' => PPost s s' [(out, 32 * d)] ∧
      bytesAt s'.mem (pa s out) (32 * d) = compressEncode d (polyAt s.mem (pa s f)) :=
  ce4At_ok hout (CEH4.of L hc hd red)

theorem ce4At_trL {f out : Ptr} {d : Nat} (hout : NA out) (hc : twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true)
    (hd : d ∈ Spec.MlKem1024.compressWidths) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f)) (ce4At f d out)
      fun _ _ => True :=
  RelCT.mono (ce4At_tr hout) (fun _ _ ⟨e, r1, r2⟩ => ⟨CEH4.of e.1 hc hd r1, CEH4.of e.2.1 hc hd r2,
    e.eq (twoChk_in hc).1, e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem dd4At_okL {s : State} (L : Lay rbs wbs s) {b f : Ptr} {d : Nat} (hf : NA f)
    (hc : twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true) (hd : d ∈ Spec.MlKem1024.compressWidths) :
    WP isa (dd4At b d f) s fun s' => PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (pa s f) (decodeDecompress d (bytesAt s.mem (pa s b) (32 * d))) :=
  dd4At_ok hf (DDH4.of L hc hd)

theorem dd4At_trL {b f : Ptr} {d : Nat} (hf : NA f) (hc : twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true)
    (hd : d ∈ Spec.MlKem1024.compressWidths) :
    RelCT isa (LRel rbs wbs) (dd4At b d f) fun _ _ => True :=
  RelCT.mono (dd4At_tr hf) (fun _ _ e => ⟨DDH4.of e.1 hc hd, DDH4.of e.2.1 hc hd, e.eq (twoChk_in hc).1,
    e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

end

/-! ## An entry of `Â` -/

/-- `SampleNTT(ρ ‖ j ‖ i)` to `a`, with `ρ` at `SB`. -/
abbrev sampP (a : Ptr) (i j : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) (sampleAt a)

theorem sampP_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {i j : Nat} (hi : i < 256) (hj : j < 256) {o : Nat}
    (hc : ijChk (rbs ++ wbs) wbs (sc o) = true) :
    WP isa (sampP (sc o) i j) s fun s' =>
      PPostB s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(sc o, 1024), (sc oSS, 2048)]) ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j)).isSome then 1 else 0)) ∧
      ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j) = some f →
        PolyIs s'.mem (pa s (sc o)) f := by
  rw [WP.seq_iff]
  refine WP.mono (setIJ_ok L hcs hi hj hc) fun s₂ ⟨hP₂, hseed⟩ => ?_
  have L₂ := L.post hP₂.b hcs
  refine WP.mono (sampleAt_ok rbx_na (SampH.of L₂ (ijChk_spec hc).1)) fun s₃ h => ?_
  have e3 : pa s₂ (sc o) = pa s (sc o) := hP₂.pa rbx_cs
  refine ⟨PPostB.app hP₂.b h.b (by simp [bases]), ?_, fun f hf => ?_⟩
  · rw [h.r15, hseed, hP₂.cs .r15 (by decide)]
  · rw [← e3]; exact h.res f (by rw [hseed]; exact hf)

theorem sampP_tr {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {i j : Nat}
    (hi : i < 256) (hj : j < 256) {o : Nat} (hc : ijChk (rbs ++ wbs) wbs (sc o) = true)
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i))
      (.block [])).isSome = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ bytesAt x.mem (pa x (sc oSB)) 32 = bytesAt y.mem (pa y (sc oSB)) 32)
      (sampP (sc o) i j) fun _ _ => True := by
  have hin : inB (rbs ++ wbs) (sc oSB) 34 = true := (sampChk_in (ijChk_spec hc).1).1
  refine RelCT.seq (RelCT.postDep (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.eq hin) ht)
    (F := fun x x' => PPost x x' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt x'.mem (pa x' (sc oSB)) 34 = matSeed (bytesAt x.mem (pa x (sc oSB)) 32) i j)
    (fun x y h => ⟨setIJ_ok h.1.1 hcs hi hj hc, setIJ_ok h.1.2.1 hcs hi hj hc⟩)
    fun x y x' y' h hx hy => ⟨h.1.post hcs hx.1.b hy.1.b, by rw [hx.2, hy.2, h.2]⟩)
    (sampleAt_trL rbx_na (ijChk_spec hc).1)

/-! ## Sums of four products -/

/-- What a sum of three products writes. -/
abbrev dot3W : List (Ptr × Nat) := [(pS 15, 1024), (sc oSS, 1024)] ++ [(pS 16, 1024), (sc oSS, 1024)] ++
  [(pS 15, 1024)] ++ [(pS 16, 1024), (sc oSS, 1024)] ++ [(pS 15, 1024)]

/-- What a sum of four products writes. -/
abbrev dot4W : List (Ptr × Nat) := dot3W ++ [(pS 16, 1024), (sc oSS, 1024)] ++ [(pS 15, 1024)]

def dot4Chk (bs wbs : List (Reg × Nat)) (f g : Nat → Ptr) : Bool :=
  dotChk bs wbs f g && keepB bs W3 (f 3) 1024 && keepB bs W3 (g 3) 1024 && decide (NA (f 3)) &&
    decide (NA (g 3)) && mulChk bs wbs (pS 16) (f 3) (g 3) && keepB bs [(pS 16, 1024), (sc oSS, 1024)] (pS 15) 1024

theorem dot4Chk_spec {bs wbs : List (Reg × Nat)} {f g : Nat → Ptr} (h : dot4Chk bs wbs f g = true) :
    dotChk bs wbs f g = true ∧ keepB bs W3 (f 3) 1024 = true ∧ keepB bs W3 (g 3) 1024 = true ∧ NA (f 3) ∧
      NA (g 3) ∧ mulChk bs wbs (pS 16) (f 3) (g 3) = true ∧
      keepB bs [(pS 16, 1024), (sc oSS, 1024)] (pS 15) 1024 = true := by
  simp only [dot4Chk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

theorem dot4_eq (a b : Nat → Poly) : dot4 a b = add (dot3 a b) (multiplyNTTs (a 3) (b 3)) := rfl

/-- The sum of products `a₀ b₀ + a₁ b₁ + a₂ b₂ + a₃ b₃`, accumulated left to right. -/
theorem dot4At_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {f g : Nat → Ptr} (hc : dot4Chk (rbs ++ wbs) wbs f g = true)
    {a b : Nat → Poly} (ha : ∀ k < 4, PolyIs s.mem (pa s (f k)) (a k)) (hb : ∀ k < 4, PolyIs s.mem (pa s (g k)) (b k)) :
    WP isa (dot4At f g) s fun s' => PPost s s' dot4W ∧ PolyIs s'.mem (pa s (pS 15)) (dot4 a b) := by
  obtain ⟨hdc, kf, kg, nf, ng, hm3, hk15⟩ := dot4Chk_spec hc
  have hac := (dotChk_spec hdc).2.2.2.2.1
  have s3 : ∀ w ∈ dot3W, w ∈ W3 := by decide
  unfold dot4At
  refine WP.seq (WP.mono (dotAt_ok L hcs hdc (fun k hk => ha k (by omega)) (fun k hk => hb k (by omega)))
    fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  have ha₁ := L.keepPoly hP₁.b (keepB_sub kf s3) (ha 3 (by decide))
  have hb₁ := L.keepPoly hP₁.b (keepB_sub kg s3) (hb 3 (by decide))
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.seq (WP.mono (mulAt_okL L₁ nf ng hm3 ha₁.1 hb₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b hcs
  rw [ha₁.2, hb₁.2, ← hP₂.pa rbx_cs] at hp₂
  have hq₂ := L₁.keepPoly hP₂.b hk15 hp₁
  refine WP.mono (addAt_ok L₂ rbx_na hac hq₂.1 hp₂.1) fun s₃ ⟨hP₃, hp₃⟩ =>
    ⟨PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide), ?_⟩
  rw [hq₂.2, hp₂.2, hP₂.pa rbx_cs, hP₁.pa rbx_cs] at hp₃
  rw [dot4_eq]; exact hp₃

/-- The inputs of a sum of four products, reduced. -/
abbrev DotIn4 (f g : Nat → Ptr) (s : State) : Prop :=
  ∀ k < 4, Reduced s.mem (pa s (f k)) ∧ Reduced s.mem (pa s (g k))

theorem dot4At_tr {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {f g : Nat → Ptr}
    (hc : dot4Chk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ DotIn4 f g x ∧ DotIn4 f g y) (dot4At f g) fun _ _ => True := by
  obtain ⟨hdc, kf, kg, nf, ng, hm3, hk15⟩ := dot4Chk_spec hc
  have hac := (dotChk_spec hdc).2.2.2.2.1
  have s3 : ∀ w ∈ dot3W, w ∈ W3 := by decide
  unfold dot4At
  refine RelCT.seqL (J := fun x => Reduced x.mem (pa x (f 3)) ∧ Reduced x.mem (pa x (g 3)) ∧
      Reduced x.mem (pa x (pS 15))) hcs
    (RelCT.mono (dotAt_tr hcs hdc) (fun _ _ ⟨e, i1, i2⟩ => ⟨e, fun k hk => i1 k (by omega), fun k hk => i2 k (by omega)⟩)
      fun _ _ h => h)
    (fun x Lx hi => WP.mono (dotAt_ok Lx hcs hdc (a := fun k => polyAt x.mem (pa x (f k)))
      (b := fun k => polyAt x.mem (pa x (g k))) (fun k hk => ⟨(hi k (by omega)).1, rfl⟩)
      (fun k hk => ⟨(hi k (by omega)).2, rfl⟩)) fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩,
        Lx.keepRed hP.b (keepB_sub kf s3) (hi 3 (by decide)).1, Lx.keepRed hP.b (keepB_sub kg s3) (hi 3 (by decide)).2,
        by rw [hP.pa rbx_cs]; exact hq.1⟩) ?_
  refine RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) hcs
    (RelCT.mono (mulAt_trL nf ng hm3) (fun _ _ ⟨e, i1, i2⟩ => ⟨e, ⟨i1.1, i1.2.1⟩, ⟨i2.1, i2.2.1⟩⟩) fun _ _ h => h)
    (fun x Lx hi => WP.mono (mulAt_okL Lx nf ng hm3 hi.1 hi.2.1) fun x' ⟨hP, hp⟩ => ⟨⟨_, hP.b⟩,
      Lx.keepRed hP.b hk15 hi.2.2, by rw [hP.pa rbx_cs]; exact hp.1⟩) ?_
  exact RelCT.mono (addAt_tr rbx_na hac) (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1, i2⟩) fun _ _ _ => trivial

end VG.Proof.MlKem1024.X86_64
