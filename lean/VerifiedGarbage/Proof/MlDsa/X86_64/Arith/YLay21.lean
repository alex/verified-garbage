import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay

/-!
# ML-DSA on x86-64: the layers of the NTT and its inverse with `len` = 2 and 1 on AVX2 registers

Each iteration of these layers loads sixteen coefficients, from `j`, into
`ymm0` and `ymm1` (or `ymm2`), and in each lane `l` runs `vlay2`'s or
`vlay1`'s gathering, butterflies and interleaving back (`Ntt.lean`) on the
four coefficients from `j + 4l` and the four from `j + 8 + 4l` (`core2_ok`,
`core1_ok`), with the zetas of their blocks in lane `l` of `ymm13`
(`yzetaS_ok`, `yzeta8_ok`, `yzeta8R_ok`); `ystep21` is an iteration for any
such code, and `ylay2_ok` and `ylay1_ok` the layers.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok ifp ifn sel sel_lt add_ofNat_zero GOnly
  addR_ok wp_rcxLoopY wp_cons_iff lane_setReg lane_setFlags State.setMem_ymm State.setMem_setMem q256lo q256hi
  lo4 hi4)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt PolyIs zetas)

/-! ## An iteration -/

/-- The body of the loop of the layers with `len` = 2 and 1. -/
abbrev ybody21 (r2 : XReg) (zl core : List Instr) (dz : BitVec 32) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0)] ++ ([.vmovdquLoad .l256 r2 (at_ .rdx 32)] ++ (zl ++
    ([.alu .add .r8 (.imm dz)] ++ (toY core ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64),
      .alu .sub .rcx (.imm 1)]))))

/-- An iteration of a layer with `len` = 2 or 1: the sixteen coefficients of
`G` from `j`, in lane `l` the four from `j + 4l` and the four from
`j + 8 + 4l`, become those of `R`, with the zetas `ζ l` that `zl` leaves in
the lanes of `ymm13`. -/
theorem ystep21 {core zl : List Instr} {r2 : XReg} {zs : List XReg} {dz : BitVec 32}
    (hY : laneSseBlock (toY core) = some core) (h0 : XReg.xmm0 ∉ zs) (h2 : r2 ∉ zs)
    (h14 : XReg.xmm14 ∉ [XReg.xmm0] ++ [r2] ++ zs) (h15 : XReg.xmm15 ∉ [XReg.xmm0] ++ [r2] ++ zs)
    (h20 : XReg.xmm0 ∉ [r2]) {fP : Addr} {j : Nat} (hj : j + 16 ≤ 256) {G R : Poly}
    {ζ : Nat → Nat → Zq} {s : State} (hc : YConsts s) (hdx : s.gpr .rdx = coeffAddr fP j)
    (hS : PolyIs s.mem fP G) (hw : pR fP ∈ s.wr)
    (hz : ∀ s', XKeep s s' →
      WP isa (.block zl) s' fun s'' => (∀ l < 2, ZLanes (s''.lane .xmm13 l) (ζ l) ∧
        ZOdd (s''.lane .xmm13 l) (s''.lane .xmm12 l)) ∧ YOnly zs s' s'')
    (hcore : ∀ l < 2, ∀ t : State, VConsts t → DLanes (t.xmm .xmm0) (fun e => G[j + 4 * l + e]!) →
      DLanes (t.xmm r2) (fun e => G[j + 8 + 4 * l + e]!) → ZLanes (t.xmm .xmm13) (ζ l) →
      ZOdd (t.xmm .xmm13) (t.xmm .xmm12) →
      WP isa (.block core) t fun t' => (DLanes (t'.xmm .xmm0) (fun e => R[j + 4 * l + e]!) ∧
        DLanes (t'.xmm .xmm1) (fun e => R[j + 8 + 4 * l + e]!)) ∧
        XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t')
    (hR : ∀ i < 256, i < j ∨ j + 16 ≤ i → R[i]! = G[i]!) :
    WP isa (.block (ybody21 r2 zl core dz)) s fun s' =>
      PolyIs s'.mem fP R ∧ s'.gpr .rdx = coeffAddr fP (j + 16) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInvY fP s s' := by
  have j0 : j + 8 ≤ 256 := by omega
  have j1 : j + 8 + 8 ≤ 256 := by omega
  have a1 : coeffAddr fP j + BitVec.ofNat 64 32 = coeffAddr fP (j + 8) := coeffAddr_add _ _ 8
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact f_in32 (List.mem_append_right s.rd hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [hdx, a1]; exact f_in32 (List.mem_append_right s.rd hw) j1
  rw [ybody21, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (d := r2) (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (hz s2 o12.toXKeep) fun s3 ⟨Z3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addR_ok .r8 dz s3) fun s4 ⟨h84, g4, y4⟩ => ?_
  have l4 := g4.lane y4
  have c4 : YConsts s4 := ylanes_gpr (s := s3) l4 (o12.trans o3) hc h14 h15
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hY (P := fun l t => DLanes (t.xmm .xmm0) (fun e => R[j + 4 * l + e]!) ∧
      DLanes (t.xmm .xmm1) (fun e => R[j + 8 + 4 * l + e]!))
    fun l hl => hcore l hl _ (c4 l hl)
      (by rw [State.proj_xmm, l4, o3.lane _ h0 l hl, o2.lane _ h20 l hl, L0 l hl, hdx, add_ofNat_zero]
          exact dlanes_loadY hS j0 hl)
      (by rw [State.proj_xmm, l4, o3.lane _ h2 l hl, L2 l hl, o1.gpr, o1.mem, hdx, a1]
          exact dlanes_loadY hS j1 hl)
      (by rw [State.proj_xmm, l4]; exact (Z3 l hl).1)
      (by rw [State.proj_xmm, State.proj_xmm, l4, l4]; exact (Z3 l hl).2)) fun s5 ⟨C5, o5⟩ => ?_
  have m5 : s5.mem = s.mem := by rw [o5.mem, g4.mem, o3.mem, o12.mem]
  have g5 : s5.gpr = s4.gpr := o5.gpr
  have dx5 : s5.gpr .rdx = coeffAddr fP j := by rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr, hdx]
  have k5 : s5.rd = s.rd ∧ s5.wr = s.wr := ⟨by rw [o5.rd, g4.keep.2.1, o3.rd, o12.rd],
    by rw [o5.wr, g4.keep.2.2, o3.wr, o12.wr]⟩
  have w0 : InRegions s5.wr (s5.gpr .rdx) 32 := by rw [k5.2, dx5]; exact f_in32 hw j0
  have w1 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 32) 32 := by rw [k5.2, dx5, a1]; exact f_in32 hw j1
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, State.setMem_setMem, w0, w1, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  rw [dx5, a1, m5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · exact polyIs_write2L (s := s5) hS j0 j1 (by omega) (fun l hl => (C5 l hl).1)
      (fun l hl => (C5 l hl).2) fun i hi _ _ => hR i hi (by omega)
  · rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) by decide, coeffAddr_add]
  · rw [g5, h84, o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, State.setMem_gpr]
    rw [g5, g4.keep.gpr (by simp [hr]), o3.gpr, o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; exact k5.1
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; exact k5.2
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact ylanes_gpr (s := s5) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o5 c4
      (by decide) (by decide)
  · exact o5.mxcsr.trans (g4.mxcsr.trans (o12.trans o3).mxcsr)

/-! ## The gatherings, the butterflies and the interleavings back of a lane -/

theorem gath2_ok (t : State) :
    WP isa (.block gath2) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm1) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm1)) ∧ XOnly [.xmm2, .xmm0, .xmm1] t t' := by
  simp only [gath2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat2_ok (t : State) :
    WP isa (.block scat2) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem gath1_ok (t : State) :
    WP isa (.block gath1) t fun t' =>
      (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm2) 0xD8) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm2) 0xD8)) ∧
        XOnly [.xmm0, .xmm2, .xmm1] t t' := by
  simp only [gath1, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat1_ok (t : State) :
    WP isa (.block scat1) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpckldq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat1, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
include hbf

/-- `vlay2`'s work on the coefficients `A` of `xmm0` and `B` of `xmm1`: the
blocks `A` and `B` of `len = 2`, with the zetas `ζ` (the first two for `A`,
the last two for `B`). -/
theorem core2_ok {t : State} (hc : VConsts t) {A B ζ : Nat → Zq} (hA : DLanes (t.xmm .xmm0) A)
    (hB : DLanes (t.xmm .xmm1) B) (hz : ZLanes (t.xmm .xmm13) ζ) (ho : ZOdd (t.xmm .xmm13) (t.xmm .xmm12)) :
    WP isa (.block (gath2 ++ bf ++ scat2)) t fun t' =>
      (DLanes (t'.xmm .xmm0) (fun e => if e < 2 then (op (A e) (A (2 + e)) (ζ e)).1
          else (op (A (e - 2)) (A e) (ζ (e - 2))).2) ∧
        DLanes (t'.xmm .xmm1) (fun e => if e < 2 then (op (B e) (B (2 + e)) (ζ (2 + e))).1
          else (op (B (e - 2)) (B e) (ζ e)).2)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (gath2_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (xonly_vconsts o1 hc (by decide) (by decide))
    (fun e => if e < 2 then A e else B (e - 2)) (fun e => if e < 2 then A (2 + e) else B e) ζ
    (fun e he => by
      dsimp only; rw [e0, dword_punpcklqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · exact hA e he
      · exact hB (e - 2) (by omega))
    (fun e he => by
      dsimp only; rw [e1, dword_punpckhqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · exact hA (2 + e) (by omega)
      · exact hB e he)
    (by rw [o1.xmm _ (by decide)]; exact hz) (by rw [o1.xmm _ (by decide), o1.xmm _ (by decide)]; exact ho))
    fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (scat2_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · rw [f0, dword_punpcklqdq _ _ he]
    split
    · rw [X e he]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›), ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›)]
    · rw [Y (e - 2) (by omega)]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show e - 2 < 2 by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show e - 2 < 2 by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›), show 2 + (e - 2) = e by omega]
  · rw [f1, dword_punpckhqdq _ _ he]
    split
    · rw [X (2 + e) (by omega)]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 2 + e < 2 by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 2 + e < 2 by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›), show 2 + e - 2 = e by omega]
    · rw [Y e he]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›), ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›)]
  · exact ((o1.trans o2).trans o3).mono (by simp)

/-- `vlay1`'s work on the coefficients `A` of `xmm0` and `B` of `xmm2`: the
blocks `A₀₁`, `A₂₃`, `B₀₁` and `B₂₃` of `len = 1`, with the zetas `ζ`. -/
theorem core1_ok {t : State} (hc : VConsts t) {A B ζ : Nat → Zq} (hA : DLanes (t.xmm .xmm0) A)
    (hB : DLanes (t.xmm .xmm2) B) (hz : ZLanes (t.xmm .xmm13) ζ) (ho : ZOdd (t.xmm .xmm13) (t.xmm .xmm12)) :
    WP isa (.block (gath1 ++ bf ++ scat1)) t fun t' =>
      (DLanes (t'.xmm .xmm0) (fun e => if e % 2 = 0 then (op (A e) (A (e + 1)) (ζ (e / 2))).1
          else (op (A (e - 1)) (A e) (ζ (e / 2))).2) ∧
        DLanes (t'.xmm .xmm1) (fun e => if e % 2 = 0 then (op (B e) (B (e + 1)) (ζ (2 + e / 2))).1
          else (op (B (e - 1)) (B e) (ζ (2 + e / 2))).2)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (gath1_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (xonly_vconsts o1 hc (by decide) (by decide))
    (fun e => if e < 2 then A (2 * e) else B (2 * (e - 2))) (fun e => if e < 2 then A (2 * e + 1) else B (2 * (e - 2) + 1))
    ζ
    (fun e he => by
      dsimp only; rw [e0, dword_punpcklqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · rw [dword_d8 _ he, ite_eq_left h]; exact hA _ (by omega)
      · rw [dword_d8 _ (by omega), ite_eq_left (by omega)]; exact hB _ (by omega))
    (fun e he => by
      dsimp only; rw [e1, dword_punpckhqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · rw [dword_d8 _ (by omega), ite_eq_right (by omega), show 2 * (2 + e - 2) + 1 = 2 * e + 1 by omega]
        exact hA _ (by omega)
      · rw [dword_d8 _ he, ite_eq_right h]; exact hB _ (by omega))
    (by rw [o1.xmm _ (by decide)]; exact hz) (by rw [o1.xmm _ (by decide), o1.xmm _ (by decide)]; exact ho))
    fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (scat1_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · rw [f0, dword_punpckldq' _ _ he]
    split
    · rw [X (e / 2) (by omega)]; dsimp only
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left ‹e % 2 = 0›,
        show 2 * (e / 2) = e by omega]
    · rw [Y (e / 2) (by omega)]; dsimp only
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right ‹¬ e % 2 = 0›,
        show 2 * (e / 2) = e - 1 by omega, show e - 1 + 1 = e by omega]
  · rw [f1, dword_punpckhdq' _ _ he]
    split
    · rw [X (2 + e / 2) (by omega)]; dsimp only
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ‹e % 2 = 0›,
        show 2 * (2 + e / 2 - 2) = e by omega]
    · rw [Y (2 + e / 2) (by omega)]; dsimp only
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right ‹¬ e % 2 = 0›,
        show 2 * (2 + e / 2 - 2) = e - 1 by omega, show e - 1 + 1 = e by omega]
  · exact ((o1.trans o2).trans o3).mono (by simp)

end

/-! ## The zetas of the layer with `len = 1` -/

/-- A doubleword of four of the zetas, at index `i` of the table. -/
theorem dword_tab {m : Mem} {zP : Addr} (ht : Tab zmTab m zP 256) {j e i : Nat} (he : e < 4) (hi : j + e = i)
    (hi' : i < 256) : (dword (m.readW (coeffAddr zP j) 128) e).toNat = (zetas i).val * 2 ^ 32 % q := by
  subst hi; rw [dword_readW _ _ he, coeffAddr_add]; exact tab_zeta ht hi'

/-- `vpermq` with `0x27`: lane 0 is `punpckhqdq` of the upper and the lower lane, lane 1 their `punpcklqdq`. -/
theorem perm27 (a b : BitVec 128) :
    permQwords (b ++ a) 0x27 = qword256 (b ++ a) 0 ++ qword256 (b ++ a) (2 + 0) ++
      qword256 (b ++ a) 1 ++ qword256 (b ++ a) (2 + 1) := rfl

theorem perm27_lo (a b : BitVec 128) :
    (permQwords (b ++ a) 0x27).extractLsb' 0 128 = XBinOp.eval .punpckhqdq b a := by
  rw [perm27, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), lo4]; rfl

theorem perm27_hi (a b : BitVec 128) :
    (permQwords (b ++ a) 0x27).extractLsb' 128 128 = XBinOp.eval .punpcklqdq b a := by
  rw [perm27, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), hi4]; rfl

/-- `vpermq d, r, 0x27`. -/
theorem ypermq27_ok {d r : XReg} (s : State) :
    WP isa (.block [.vop (.vpermq d r 0x27)]) s fun s' =>
      s'.lane d 0 = XBinOp.eval .punpckhqdq (s.lane r 1) (s.lane r 0) ∧
      s'.lane d 1 = XBinOp.eval .punpcklqdq (s.lane r 1) (s.lane r 0) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r' hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, ifp rfl, State.ymm_eq, perm27_lo]
  · rw [State.lane_setV256, ifp rfl, ifn (by decide), State.ymm_eq, perm27_hi]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-- The eight zetas at index `k` of the table, in the order of the blocks of
`ylay1` for `NTT`: in lane `l`, zetas `k + 2l`, `k + 2l + 1`, `k + 2l + 4`
and `k + 2l + 5`. -/
theorem yzeta8_ok {zP : Addr} {k : Nat} (hk : k + 8 ≤ 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 32) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block yzeta8) s fun s' =>
      (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun e => zetas (k + (2 * l + e + 2 * (e / 2)))) ∧
        ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta8, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (yld_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.ypermq_ok s1) fun s2 ⟨e0, e1, o2⟩ => ?_
  refine WP.mono (yF5_ok s2) fun s3 ⟨f3, o3⟩ => ⟨fun l hl => ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  rw [f3 l hl, o3.lane _ (by decide) l hl]
  refine ⟨fun e he => ?_, zodd_F5 _⟩
  have a : ∀ l < 2, s1.lane .xmm13 l = s.mem.readW (coeffAddr zP (k + 4 * l)) 128 := fun l hl => by
    rw [L1 l hl, h8, add_ofNat_zero, lane_load]
  rcases lane01 hl with rfl | rfl
  · rw [e0, dword_punpcklqdq _ _ he, a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht he (by omega) (by omega)
    · exact dword_tab ht (by omega) (by omega) (by omega)
  · rw [e1, dword_punpckhqdq _ _ he, a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht (by omega) (by omega) (by omega)
    · exact dword_tab ht he (by omega) (by omega)

theorem dword_b1 (x : BitVec 128) {e : Nat} (he : e < 4) :
    dword (shufDwords x 0xB1) e = dword x (if e % 2 = 0 then e + 1 else e - 1) := by
  rw [dword_shufDwords _ _ he]
  rcases cases4 he with rfl | rfl | rfl | rfl <;> rfl

theorem zsseR_ok (t : State) :
    WP isa (.block [.xop (.pshufd .xmm13 .xmm13 0xB1), .xop (.pshufd .xmm12 .xmm13 0xF5)]) t fun t' =>
      (t'.xmm .xmm13 = shufDwords (t.xmm .xmm13) 0xB1 ∧
        t'.xmm .xmm12 = shufDwords (shufDwords (t.xmm .xmm13) 0xB1) 0xF5) ∧ XOnly [.xmm13, .xmm12] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

/-- The eight zetas at index `k` of the table, in the order of the blocks of
`ylay1` for `NTT⁻¹`, which take them in decreasing order: in lane `l`, zetas
`k + 7 - 2l`, `k + 6 - 2l`, `k + 3 - 2l` and `k + 2 - 2l`. -/
theorem yzeta8R_ok {zP : Addr} {k : Nat} (hk : k + 8 ≤ 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 32) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block yzeta8R) s fun s' =>
      (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun e => zetas (k + 7 - (2 * l + e + 2 * (e / 2)))) ∧
        ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta8R, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (yld_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (ypermq27_ok s1) fun s2 ⟨e0, e1, o2⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm13 = shufDwords (s2.lane .xmm13 l) 0xB1 ∧
      t.xmm .xmm12 = shufDwords (shufDwords (s2.lane .xmm13 l) 0xB1) 0xF5)
    fun l _ => zsseR_ok (s2.proj l)) fun s3 ⟨l3, o3⟩ => ⟨fun l hl => ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  have e13 : s3.lane .xmm13 l = _ := (l3 l hl).1
  have e12 : s3.lane .xmm12 l = _ := (l3 l hl).2
  rw [e12, e13]
  refine ⟨fun e he => ?_, zodd_F5 _⟩
  have a : ∀ l < 2, s1.lane .xmm13 l = s.mem.readW (coeffAddr zP (k + 4 * l)) 128 := fun l hl => by
    rw [L1 l hl, h8, add_ofNat_zero, lane_load]
  have he' : (if e % 2 = 0 then e + 1 else e - 1) < 4 := by split <;> omega
  rw [dword_b1 _ he]
  generalize hf : (if e % 2 = 0 then e + 1 else e - 1) = f at he'
  have hf' : f = if e % 2 = 0 then e + 1 else e - 1 := hf.symm
  rcases lane01 hl with rfl | rfl
  · rw [e0, dword_punpckhqdq _ _ he', a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht (by omega) (by split at hf' <;> omega) (by omega)
    · exact dword_tab ht he' (by split at hf' <;> omega) (by omega)
  · rw [e1, dword_punpcklqdq _ _ he', a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht he' (by split at hf' <;> omega) (by omega)
    · exact dword_tab ht (by omega) (by split at hf' <;> omega) (by omega)

/-! ## The layers -/

section
variable {op : Zq → Zq → Zq → Zq × Zq} {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hblk

/-- The sixteen coefficients from `16i` after the next blocks of the layer
with `len = 2`. -/
theorem layF2_next (F : Poly) (zi : Nat → Nat) {i : Nat} (hi : i < 16) {x : Nat} (hx : x < 256) :
    (layF blk F 2 zi (4 * (i + 1)))[x]! = if 16 * i ≤ x ∧ x < 16 * i + 16 then
      (if x % (2 * 2) < 2 then
        (op (layF blk F 2 zi (4 * i))[x]! (layF blk F 2 zi (4 * i))[x + 2]! (zetas (zi (x / (2 * 2))))).1
      else (op (layF blk F 2 zi (4 * i))[x - 2]! (layF blk F 2 zi (4 * i))[x]! (zetas (zi (x / (2 * 2))))).2)
      else (layF blk F 2 zi (4 * i))[x]! := by
  have hF : ∀ y, 16 * i ≤ y → y < 256 → (layF blk F 2 zi (4 * i))[y]! = F[y]! := fun y h1 h2 => by
    rw [layF_get hblk F (by decide) zi (by omega) h2, ite_eq_right (by omega)]
  rw [layF_get hblk F (by decide) zi (by omega) hx]
  by_cases h1 : 16 * i ≤ x ∧ x < 16 * i + 16
  · rw [ite_eq_left (by omega), ite_eq_left h1]
    by_cases h2 : x % (2 * 2) < 2
    · rw [ite_eq_left h2, ite_eq_left h2, hF _ h1.1 hx, hF _ (by omega) (by omega)]
    · rw [ite_eq_right h2, ite_eq_right h2, hF _ (by omega) (by omega), hF _ h1.1 hx]
  · rw [ite_eq_right h1, layF_get hblk F (by decide) zi (by omega) hx]
    by_cases h3 : x < 16 * i
    · rw [ite_eq_left (show x < 2 * 2 * (4 * (i + 1)) by omega), ite_eq_left (show x < 2 * 2 * (4 * i) by omega)]
    · rw [ite_eq_right (show ¬ x < 2 * 2 * (4 * (i + 1)) by omega),
        ite_eq_right (show ¬ x < 2 * 2 * (4 * i) by omega)]

/-- The sixteen coefficients from `16i` after the next blocks of the layer
with `len = 1`. -/
theorem layF1_next (F : Poly) (zi : Nat → Nat) {i : Nat} (hi : i < 16) {x : Nat} (hx : x < 256) :
    (layF blk F 1 zi (8 * (i + 1)))[x]! = if 16 * i ≤ x ∧ x < 16 * i + 16 then
      (if x % (2 * 1) < 1 then
        (op (layF blk F 1 zi (8 * i))[x]! (layF blk F 1 zi (8 * i))[x + 1]! (zetas (zi (x / (2 * 1))))).1
      else (op (layF blk F 1 zi (8 * i))[x - 1]! (layF blk F 1 zi (8 * i))[x]! (zetas (zi (x / (2 * 1))))).2)
      else (layF blk F 1 zi (8 * i))[x]! := by
  have hF : ∀ y, 16 * i ≤ y → y < 256 → (layF blk F 1 zi (8 * i))[y]! = F[y]! := fun y h1 h2 => by
    rw [layF_get hblk F (by decide) zi (by omega) h2, ite_eq_right (by omega)]
  rw [layF_get hblk F (by decide) zi (by omega) hx]
  by_cases h1 : 16 * i ≤ x ∧ x < 16 * i + 16
  · rw [ite_eq_left (by omega), ite_eq_left h1]
    by_cases h2 : x % (2 * 1) < 1
    · rw [ite_eq_left h2, ite_eq_left h2, hF _ h1.1 hx, hF _ (by omega) (by omega)]
    · rw [ite_eq_right h2, ite_eq_right h2, hF _ (by omega) (by omega), hF _ h1.1 hx]
  · rw [ite_eq_right h1, layF_get hblk F (by decide) zi (by omega) hx]
    by_cases h3 : x < 16 * i
    · rw [ite_eq_left (show x < 2 * 1 * (8 * (i + 1)) by omega), ite_eq_left (show x < 2 * 1 * (8 * i) by omega)]
    · rw [ite_eq_right (show ¬ x < 2 * 1 * (8 * (i + 1)) by omega),
        ite_eq_right (show ¬ x < 2 * 1 * (8 * i) by omega)]

variable {bf : List Instr} (hbf : VBflyOk bf op)
include hbf

theorem ylay2_ok (hY : laneSseBlock (toY (gath2 ++ bf ++ scat2)) = some (gath2 ++ bf ++ scat2)) {fP sP : Addr}
    (k : Nat) (o₀ o₁ : BitVec 8) (dz : BitVec 32) (zi kb : Nat → Nat) (hkb0 : kb 0 = k)
    (hk : ∀ i < 16, kb i + 4 ≤ 256)
    (hsel : ∀ i < 16, ∀ e < 4, kb i + sel o₀ e = zi (4 * i + 2 * (e / 2)) ∧
      kb i + sel o₁ e = zi (4 * i + 1 + 2 * (e / 2)))
    (hstep : ∀ i < 16, coeffAddr sP (kb i) + BitVec.signExtend 64 dz = coeffAddr sP (kb (i + 1)))
    {F : Poly} {s : State} (hc : YConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay2 bf k o₀ o₁ dz) s fun s' => PolyIs s'.mem fP (layF blk F 2 zi 64) ∧ BInvY fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (ypre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 2 zi (4 * i)) ∧ u.gpr .rdx = coeffAddr fP (16 * i) ∧
      u.gpr .r8 = coeffAddr sP (kb i) ∧ BInvY fP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkb0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        ylanes_gpr (s := w) (ou.lane hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  have hk0' : ∀ j < 4, kb i + sel o₀ j < 256 := fun j _ => by have := sel_lt o₀ j; have := hk i hi; omega
  have hk1' : ∀ j < 4, kb i + sel o₁ j < 256 := fun j _ => by have := sel_lt o₁ j; have := hk i hi; omega
  rw [show [Instr.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm1 (at_ .rdx 32)] ++ yzetaS o₀ o₁ ++
      [.alu .add .r8 (.imm dz)] ++ toY (gath2 ++ bf ++ scat2) ++
      [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1,
        .alu .add .rdx (.imm 64)] ++ [.alu .sub .rcx (.imm 1)] =
      ybody21 .xmm1 (yzetaS o₀ o₁) (gath2 ++ bf ++ scat2) dz by simp [List.append_assoc]]
  have hR := fun x hx => layF2_next hblk F zi hi (x := x) hx
  refine WP.mono (ystep21 hY (zs := [.xmm13, .xmm2, .xmm12]) (by decide) (by decide) (by decide) (by decide)
    (by decide) (j := 16 * i) (by omega) (R := layF blk F 2 zi (4 * (i + 1)))
    (ζ := fun l e => zetas (zi (4 * i + l + 2 * (e / 2)))) hb'.consts hdx' hS' hwf' (fun s' k' => ?_)
    (fun l hl t ht hA hB hz ho => ?_) (fun x hx h => by rw [hR x hx, ite_eq_right (by omega)]))
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', by rw [hdx'', Nat.mul_succ],
      by rw [h8'', h8', hstep i hi], hb'.trans hb''⟩, hcx, hzf⟩
  · -- the zetas
    refine WP.mono (yzetaS_ok o₀ o₁ (zP := sP) (k := kb i) hk0' hk1' (by rw [k'.gpr, h8'])
      (by rw [k'.rd, k'.wr]; exact tab_in (List.mem_append_right _ hw') (hk i hi)) (by rw [k'.mem]; exact hT'))
      fun s'' ⟨Z0, Z1, ZO, o⟩ => ⟨fun l hl => ⟨?_, ZO l hl⟩, o⟩
    rcases lane01 hl with rfl | rfl
    · exact Z0.congr fun e he => congrArg zetas ((hsel i hi e he).1.trans (congrArg zi (by omega)))
    · exact Z1.congr fun e he => congrArg zetas ((hsel i hi e he).2.trans (congrArg zi (by omega)))
  · -- the blocks of a lane
    refine WP.mono (core2_ok hbf ht hA hB hz ho) fun t' ⟨⟨a, b⟩, o⟩ =>
      ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
    · by_cases h : e < 2
      · rw [ite_eq_left h, hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
        exact congrArg Prod.fst (op_idx op _ zi (by omega) (by omega) (by omega))
      · rw [ite_eq_right h, hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
        exact congrArg Prod.snd (op_idx op _ zi (by omega) (by omega) (by omega))
    · by_cases h : e < 2
      · rw [ite_eq_left h, hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
        exact congrArg Prod.fst (op_idx op _ zi (by omega) (by omega) (by omega))
      · rw [ite_eq_right h, hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
        exact congrArg Prod.snd (op_idx op _ zi (by omega) (by omega) (by omega))

theorem ylay1_ok (hY : laneSseBlock (toY (gath1 ++ bf ++ scat1)) = some (gath1 ++ bf ++ scat1)) {fP sP : Addr}
    (k : Nat) (zl : List Instr) (dz : BitVec 32) (zi kb : Nat → Nat) (hkb0 : kb 0 = k)
    (hk : ∀ i < 16, kb i + 8 ≤ 256)
    (hzl : ∀ i < 16, ∀ s : State, s.gpr .r8 = coeffAddr sP (kb i) →
      InRegions (s.rd ++ s.wr) (coeffAddr sP (kb i)) 32 → Tab zmTab s.mem sP 256 →
      WP isa (.block zl) s fun s' => (∀ l < 2, ZLanes (s'.lane .xmm13 l)
          (fun e => zetas (zi (8 * i + 2 * l + e + 2 * (e / 2)))) ∧ ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧
        YOnly [.xmm13, .xmm12] s s')
    (hstep : ∀ i < 16, coeffAddr sP (kb i) + BitVec.signExtend 64 dz = coeffAddr sP (kb (i + 1)))
    {F : Poly} {s : State} (hc : YConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay1 bf k zl dz) s fun s' => PolyIs s'.mem fP (layF blk F 1 zi 128) ∧ BInvY fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (ypre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 1 zi (8 * i)) ∧ u.gpr .rdx = coeffAddr fP (16 * i) ∧
      u.gpr .r8 = coeffAddr sP (kb i) ∧ BInvY fP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkb0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        ylanes_gpr (s := w) (ou.lane hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [Instr.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm2 (at_ .rdx 32)] ++ zl ++
      [.alu .add .r8 (.imm dz)] ++ toY (gath1 ++ bf ++ scat1) ++
      [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1,
        .alu .add .rdx (.imm 64)] ++ [.alu .sub .rcx (.imm 1)] =
      ybody21 .xmm2 zl (gath1 ++ bf ++ scat1) dz by simp [List.append_assoc]]
  have hR := fun x hx => layF1_next hblk F zi hi (x := x) hx
  refine WP.mono (ystep21 hY (zs := [.xmm13, .xmm12]) (by decide) (by decide) (by decide) (by decide)
    (by decide) (j := 16 * i) (by omega) (R := layF blk F 1 zi (8 * (i + 1)))
    (ζ := fun l e => zetas (zi (8 * i + 2 * l + e + 2 * (e / 2)))) hb'.consts hdx' hS' hwf'
    (fun s' k' => hzl i hi s' (by rw [k'.gpr, h8'])
      (by rw [k'.rd, k'.wr]; exact f_in32 (List.mem_append_right _ hw') (hk i hi)) (by rw [k'.mem]; exact hT'))
    (fun l hl t ht hA hB hz ho => ?_) (fun x hx h => by rw [hR x hx, ite_eq_right (by omega)]))
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', by rw [hdx'', Nat.mul_succ],
      by rw [h8'', h8', hstep i hi], hb'.trans hb''⟩, hcx, hzf⟩
  -- the blocks of a lane
  refine WP.mono (core1_ok hbf ht hA hB hz ho) fun t' ⟨⟨a, b⟩, o⟩ =>
    ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
  · by_cases h : e % 2 = 0
    · rw [ite_eq_left h, hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      exact congrArg Prod.fst (op_idx op _ zi (by omega) (by omega) (by omega))
    · rw [ite_eq_right h, hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
      exact congrArg Prod.snd (op_idx op _ zi (by omega) (by omega) (by omega))
  · by_cases h : e % 2 = 0
    · rw [ite_eq_left h, hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      exact congrArg Prod.fst (op_idx op _ zi (by omega) (by omega) (by omega))
    · rw [ite_eq_right h, hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
      exact congrArg Prod.snd (op_idx op _ zi (by omega) (by omega) (by omega))

end

end VG.Proof.MlDsa.X86_64.Arith
