import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse with `len` = 4 and 2 on AVX2 registers

Untrusted: everything here is checked by Lean. Each iteration of these
layers loads 32 words, from `j`, into `ymm0` and `ymm4`, and in each lane
`l` runs `vlay4`'s or `vlay2`'s gathering, butterflies and interleaving
back (`Ntt.lean`) on the eight words from `j + 8l` and the eight from
`j + 16 + 8l` (`core4_ok`, `core2_ok`), with the zetas of their blocks in
lane `l` of `ymm13` (`yzetaS_ok`, `yzeta8_ok`); `ystep42` is an iteration
for any such code, and `ylay4_ok` and `ylay2_ok` the layers.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The body of the loop of `ylay42`. -/
abbrev ybody42 (core zeta : List Instr) (dz : BitVec 32) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0)] ++ ([.vmovdquLoad .l256 .xmm4 (at_ .rdx 32)] ++ (zeta ++
    ([.alu .add .r8 (.imm dz)] ++ (toY core ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64),
      .alu .sub .rcx (.imm 1)]))))

/-- An iteration of a layer with `len` = 4 or 2: the 32 words of `G` from `j`,
in lane `l` the eight from `j + 8l` and the eight from `j + 16 + 8l`, become
those of `R`, with the zetas `ζ l` that `zeta` leaves in the lanes of `ymm13`. -/
theorem ystep42 {core zeta : List Instr} {dz : BitVec 32} (hY : laneSseBlock (toY core) = some core)
    {sP : Addr} {j : Nat} (hj : j + 32 ≤ 256) {G R : Poly} {ζ : Nat → Nat → Zq} {s : State} (hc : YConsts s)
    (hdx : s.gpr .rdx = wAddr (spW sP) j) (hS : S16 s.mem (spW sP) G) (hw : pR sP ∈ s.wr)
    (hz : ∀ s', XKeep s s' →
      WP isa (.block zeta) s' fun s'' => (∀ l < 2, ZLanes (s''.lane .xmm13 l) (ζ l)) ∧
        YOnly [.xmm13, .xmm2, .xmm1] s' s'')
    (hcore : ∀ l < 2, ∀ t : State, VConsts t → Lanes (t.xmm .xmm0) (fun e => G[j + 8 * l + e]!) →
      Lanes (t.xmm .xmm4) (fun e => G[j + 16 + 8 * l + e]!) → ZLanes (t.xmm .xmm13) (ζ l) →
      WP isa (.block core) t fun t' => (Lanes (t'.xmm .xmm0) (fun e => R[j + 8 * l + e]!) ∧
        Lanes (t'.xmm .xmm1) (fun e => R[j + 16 + 8 * l + e]!)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t')
    (hR : ∀ i < 256, i < j ∨ j + 32 ≤ i → R[i]! = G[i]!) :
    WP isa (.block (ybody42 core zeta dz)) s fun s' =>
      S16 s'.mem (spW sP) R ∧ s'.gpr .rdx = wAddr (spW sP) (j + 32) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInvY sP s s' := by
  have j0 : j + 16 ≤ 256 := by omega
  have j1 : j + 16 + 16 ≤ 256 := by omega
  have a1 : wAddr (spW sP) j + BitVec.ofNat 64 32 = wAddr (spW sP) (j + 16) := wAddr_add _ _ 16
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact sp_inY (List.mem_append_right s.rd hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [hdx, a1]; exact sp_inY (List.mem_append_right s.rd hw) j1
  rw [ybody42, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L4, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (hz s2 o12.toXKeep) fun s3 ⟨Z3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addR_ok .r8 dz s3) fun s4 ⟨h84, g4, y4⟩ => ?_
  have l4 := GOnly.lane g4 y4
  have c4 : YConsts s4 := lanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hY (P := fun l t => Lanes (t.xmm .xmm0) (fun e => R[j + 8 * l + e]!) ∧
      Lanes (t.xmm .xmm1) (fun e => R[j + 16 + 8 * l + e]!))
    fun l hl => hcore l hl _ (c4 l hl)
      (by rw [State.proj_xmm, l4, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl, L0 l hl, hdx,
        add_ofNat_zero]; exact (lanes_loadY hS j0 hl).congr fun _ _ => rfl)
      (by rw [State.proj_xmm, l4, o3.lane _ (by decide) l hl, L4 l hl, o1.gpr, o1.mem, hdx, a1]
          exact (lanes_loadY hS j1 hl).congr fun _ _ => rfl)
      (by rw [State.proj_xmm, l4]; exact Z3 l hl)) fun s5 ⟨C5, o5⟩ => ?_
  have m5 : s5.mem = s.mem := by rw [o5.mem, g4.mem, o3.mem, o12.mem]
  have g5 : s5.gpr = s4.gpr := o5.gpr
  have dx5 : s5.gpr .rdx = wAddr (spW sP) j := by rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr, hdx]
  have k5 : s5.rd = s.rd ∧ s5.wr = s.wr := ⟨by rw [o5.rd, g4.keep.2.1, o3.rd, o12.rd],
    by rw [o5.wr, g4.keep.2.2, o3.wr, o12.wr]⟩
  have w0 : InRegions s5.wr (s5.gpr .rdx) 32 := by rw [k5.2, dx5]; exact sp_inY hw j0
  have w1 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 32) 32 := by rw [k5.2, dx5, a1]; exact sp_inY hw j1
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1]
  rw [dx5, a1, m5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · refine s16_write2Y (s := s5) hS j0 j1 (by omega) (a := fun e => R[j + e]!) (b := fun e => R[j + 16 + e]!)
      (fun l hl => ((C5 l hl).1).congr fun e _ => by rw [show j + 8 * l + e = j + (8 * l + e) by omega])
      (fun l hl => ((C5 l hl).2).congr fun e _ => by
        rw [show j + 16 + 8 * l + e = j + 16 + (8 * l + e) by omega]) fun i hi => ?_
    by_cases h1 : j ≤ i ∧ i < j + 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), show j + (i - j) = i by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : j + 16 ≤ i ∧ i < j + 16 + 16
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), show j + 16 + (i - (j + 16)) = i by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]; exact hR i hi (by omega)
  · rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) by decide, wAddr_add]
  · rw [g5, h84, o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, State.setMem_gpr]
    rw [g5, g4.keep.gpr (by simp [hr]), o3.gpr, o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; exact k5.1
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; exact k5.2
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact lanes_gpr (s := s5) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o5 c4
      (by decide) (by decide)
  · exact o5.mxcsr.trans (g4.mxcsr.trans (o12.trans o3).mxcsr)

/-! ## The gatherings, the butterflies and the interleavings back of a lane -/

theorem gath4_ok (t : State) :
    WP isa (.block gath4) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm4) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm4)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [gath4, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat4_ok (t : State) :
    WP isa (.block scat4) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat4, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem gath2_ok (t : State) :
    WP isa (.block gath2) t fun t' =>
      (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm4) 0xD8) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm4) 0xD8)) ∧
        XOnly [.xmm0, .xmm4, .xmm1] t t' := by
  simp only [gath2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat2_ok (t : State) :
    WP isa (.block scat2) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpckldq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
include hbf

/-- `vlay4`'s work on the words `A` of `xmm0` and `B` of `xmm4`: the blocks
`A` and `B` of `len = 4`, with the zetas `ζ` (the first four words for the
lower halves, the last four for the upper halves). -/
theorem core4_ok {t : State} (hc : VConsts t) {A B ζ : Nat → Zq} (hA : Lanes (t.xmm .xmm0) A)
    (hB : Lanes (t.xmm .xmm4) B) (hz : ZLanes (t.xmm .xmm13) ζ) :
    WP isa (.block (gath4 ++ bf ++ scat4)) t fun t' =>
      (Lanes (t'.xmm .xmm0) (fun e => if e < 4 then (op (A e) (A (4 + e)) (ζ e)).1
          else (op (A (e - 4)) (A e) (ζ (e - 4))).2) ∧
        Lanes (t'.xmm .xmm1) (fun e => if e < 4 then (op (B e) (B (4 + e)) (ζ (4 + e))).1
          else (op (B (e - 4)) (B e) (ζ e)).2)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (gath4_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (o1.consts hc (by decide) (by decide))
    (fun e => if e < 4 then A e else B (e - 4)) (fun e => if e < 4 then A (4 + e) else B e) ζ
    (fun e he => by
      dsimp only; rw [e0, word_punpcklqdq _ _ he]
      by_cases h : e < 4 <;> simp only [h, ite_true, ite_false]
      · exact hA e he
      · exact hB (e - 4) (by omega))
    (fun e he => by
      dsimp only; rw [e1, word_punpckhqdq _ _ he]
      by_cases h : e < 4 <;> simp only [h, ite_true, ite_false]
      · exact hA (4 + e) (by omega)
      · exact hB e he)
    (by rw [o1.xmm _ (by decide)]; exact hz)) fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (scat4_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · rw [f0, word_punpcklqdq _ _ he]
    split
    · rw [X e he]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›), ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›)]
    · rw [Y (e - 4) (by omega)]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show e - 4 < 4 by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show e - 4 < 4 by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›), show 4 + (e - 4) = e by omega]
  · rw [f1, word_punpckhqdq _ _ he]
    split
    · rw [X (4 + e) (by omega)]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + e < 4 by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + e < 4 by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›), show 4 + e - 4 = e by omega]
    · rw [Y e he]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›), ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›)]
  · exact ((o1.trans o2).trans o3).mono (by simp)

/-- `vlay2`'s work on the words `A` of `xmm0` and `B` of `xmm4`: the blocks
`A` and `B` of `len = 2`, with the zetas `ζ` (by doubleword, of the blocks
`A₀₋₃`, `A₄₋₇`, `B₀₋₃`, `B₄₋₇`). -/
theorem core2_ok {t : State} (hc : VConsts t) {A B ζ : Nat → Zq} (hA : Lanes (t.xmm .xmm0) A)
    (hB : Lanes (t.xmm .xmm4) B) (hz : ZLanes (t.xmm .xmm13) ζ) :
    WP isa (.block (gath2 ++ bf ++ scat2)) t fun t' =>
      (Lanes (t'.xmm .xmm0) (fun i => if i % 4 < 2 then (op (A i) (A (i + 2)) (ζ (2 * (i / 4) + i % 2))).1
          else (op (A (i - 2)) (A i) (ζ (2 * (i / 4) + i % 2))).2) ∧
        Lanes (t'.xmm .xmm1) (fun i => if i % 4 < 2 then (op (B i) (B (i + 2)) (ζ (4 + 2 * (i / 4) + i % 2))).1
          else (op (B (i - 2)) (B i) (ζ (4 + 2 * (i / 4) + i % 2))).2)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (gath2_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (o1.consts hc (by decide) (by decide))
    (fun e => if e < 4 then A (4 * (e / 2) + e % 2) else B (4 * ((e - 4) / 2) + e % 2))
    (fun e => if e < 4 then A (4 * (e / 2) + 2 + e % 2) else B (4 * ((e - 4) / 2) + 2 + e % 2)) ζ
    (fun e he => by
      dsimp only; rw [e0, word_punpcklqdq _ _ he]
      by_cases h : e < 4 <;> simp only [h, ite_true, ite_false]
      · rw [word_d8 _ (by omega), ite_eq_left_of_eq_true _ _ (eq_true h)]; exact hA _ (by omega)
      · rw [word_d8 _ (by omega), ite_eq_left_of_eq_true _ _ (eq_true (show e - 4 < 4 by omega)),
          show (e - 4) / 2 = (e - 4) / 2 by rfl, show (e - 4) % 2 = e % 2 by omega]
        exact hB _ (by omega))
    (fun e he => by
      dsimp only; rw [e1, word_punpckhqdq _ _ he]
      by_cases h : e < 4 <;> simp only [h, ite_true, ite_false]
      · rw [word_d8 _ (by omega), ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + e < 4 by omega)),
          show (4 + e - 4) / 2 = e / 2 by omega, show (4 + e) % 2 = e % 2 by omega]
        exact hA _ (by omega)
      · rw [word_d8 _ (by omega), ite_eq_right_of_eq_false _ _ (eq_false h)]; exact hB _ (by omega))
    (by rw [o1.xmm _ (by decide)]; exact hz)) fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (scat2_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
  · rw [f0, word_punpckldq _ _ hi]
    have hw : 2 * (i / 4) + i % 2 < 8 := by omega
    by_cases h : i % 4 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i / 2 % 2 = 0 by omega)), X _ hw]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (show 2 * (i / 4) + i % 2 < 4 by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show 2 * (i / 4) + i % 2 < 4 by omega)),
        show 4 * ((2 * (i / 4) + i % 2) / 2) + (2 * (i / 4) + i % 2) % 2 = i by omega,
        show 4 * ((2 * (i / 4) + i % 2) / 2) + 2 + (2 * (i / 4) + i % 2) % 2 = i + 2 by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i / 2 % 2 = 0 by omega)), Y _ hw]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        ite_eq_left_of_eq_true _ _ (eq_true (show 2 * (i / 4) + i % 2 < 4 by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show 2 * (i / 4) + i % 2 < 4 by omega)),
        show 4 * ((2 * (i / 4) + i % 2) / 2) + (2 * (i / 4) + i % 2) % 2 = i - 2 by omega,
        show 4 * ((2 * (i / 4) + i % 2) / 2) + 2 + (2 * (i / 4) + i % 2) % 2 = i by omega]
  · rw [f1, word_punpckhdq _ _ hi]
    have hw : 4 + 2 * (i / 4) + i % 2 < 8 := by omega
    by_cases h : i % 4 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i / 2 % 2 = 0 by omega)), X _ hw]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true h),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + 2 * (i / 4) + i % 2 < 4 by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + 2 * (i / 4) + i % 2 < 4 by omega)),
        show 4 * ((4 + 2 * (i / 4) + i % 2 - 4) / 2) + (4 + 2 * (i / 4) + i % 2) % 2 = i by omega,
        show 4 * ((4 + 2 * (i / 4) + i % 2 - 4) / 2) + 2 + (4 + 2 * (i / 4) + i % 2) % 2 = i + 2 by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i / 2 % 2 = 0 by omega)), Y _ hw]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + 2 * (i / 4) + i % 2 < 4 by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + 2 * (i / 4) + i % 2 < 4 by omega)),
        show 4 * ((4 + 2 * (i / 4) + i % 2 - 4) / 2) + (4 + 2 * (i / 4) + i % 2) % 2 = i - 2 by omega,
        show 4 * ((4 + 2 * (i / 4) + i % 2 - 4) / 2) + 2 + (4 + 2 * (i / 4) + i % 2) % 2 = i by omega]
  · exact ((o1.trans o2).trans o3).mono (by simp)

end

/-! ## The layers -/

/-- A layer of eight iterations of `ystep42`, iteration `m` turning `Gs m`
into `Gs (m + 1)`, with `r8` at word `t + c m` of the table. -/
theorem ylay42_loop {bf gath scat zeta : List Instr} {dz : BitVec 32}
    (hY : laneSseBlock (toY (gath ++ bf ++ scat)) = some (gath ++ bf ++ scat)) {sP : Addr} {t : Nat} (ht : t < 128)
    (c : Nat → Nat) (hc0 : c 0 = 0) (hdz : ∀ m < 8, wAddr sP (t + c m) + BitVec.signExtend 64 dz = wAddr sP (t + c (m + 1)))
    {z : Nat → Zq} (Gs : Nat → Poly) (ζ : Nat → Nat → Nat → Zq)
    (hz : ∀ m < 8, ∀ s' : State, s'.gpr .r8 = wAddr sP (t + c m) → TZ s'.mem sP z → pR sP ∈ s'.wr →
      WP isa (.block zeta) s' fun s'' => (∀ l < 2, ZLanes (s''.lane .xmm13 l) (ζ m l)) ∧
        YOnly [.xmm13, .xmm2, .xmm1] s' s'')
    (hcore : ∀ m < 8, ∀ l < 2, ∀ t' : State, VConsts t' → Lanes (t'.xmm .xmm0) (fun e => (Gs m)[32 * m + 8 * l + e]!) →
      Lanes (t'.xmm .xmm4) (fun e => (Gs m)[32 * m + 16 + 8 * l + e]!) → ZLanes (t'.xmm .xmm13) (ζ m l) →
      WP isa (.block (gath ++ bf ++ scat)) t' fun t'' =>
        (Lanes (t''.xmm .xmm0) (fun e => (Gs (m + 1))[32 * m + 8 * l + e]!) ∧
          Lanes (t''.xmm .xmm1) (fun e => (Gs (m + 1))[32 * m + 16 + 8 * l + e]!)) ∧
        XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t' t'')
    (hR : ∀ m < 8, ∀ i < 256, i < 32 * m ∨ 32 * m + 32 ≤ i → (Gs (m + 1))[i]! = (Gs m)[i]!)
    {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) (Gs 0))
    (hT : TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay42 bf gath scat zeta dz t) s fun s' => S16 s'.mem (spW sP) (Gs 8) ∧ BInvY sP s s' := by
  refine WP.seq (WP.mono (ypre_ok t ht hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := lanes_gpr (s := s) (GOnly.lane og hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide)
    (fun i u => S16 u.mem (spW sP) (Gs i) ∧ u.gpr .rdx = wAddr (spW sP) (32 * i) ∧
      u.gpr .r8 = wAddr sP (t + c i) ∧ BInvY sP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, wAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hc0, Nat.add_zero], ⟨ou.keep.mono (by simp),
        by rw [ou.mem]; exact Frame.refl _ _,
        lanes_gpr (s := w) (GOnly.lane ou hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : TZ u.mem sP z := (by rw [og.mem]; exact hT : TZ w.mem sP z).frame hb'.frame
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm4 (at_ .rdx 32)] ++ zeta ++
      [.alu .add .r8 (.imm dz)] ++ toY (gath ++ bf ++ scat) ++
      [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64)] ++
      [.alu .sub .rcx (.imm 1)] = ybody42 (gath ++ bf ++ scat) zeta dz by simp [List.append_assoc]]
  refine WP.mono (ystep42 hY (j := 32 * i) (by omega) hb'.consts hdx' hS' hw'
    (fun s' k => hz i hi s' (by rw [k.gpr, h8']) (by rw [k.mem]; exact hT') (by rw [k.wr]; exact hw'))
    (hcore i hi) (hR i hi))
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', by rw [hdx'', Nat.mul_succ],
      by rw [h8'', h8', hdz i hi], hb'.trans hb''⟩, hcx, hzf⟩

theorem sel_A0 {j : Nat} (hj : j < 4) : sel 0xA0 j = 2 * (j / 2) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

theorem sel_F5 {j : Nat} (hj : j < 4) : sel 0xF5 j = 1 + 2 * (j / 2) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem ylay4_ok (hY : laneSseBlock (toY (gath4 ++ bf ++ scat4)) = some (gath4 ++ bf ++ scat4))
    {sP : Addr} {t : Nat} (zi : Nat → Nat) {z : Nat → Zq}
    (hz : ∀ c < 32, t + c < 128 ∧ z (t + c) = zeta (zi c))
    {F : Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 bf t) s fun s' => S16 s'.mem (spW sP) (layF blk F 4 zi 32) ∧ BInvY sP s s' := by
  have ht : t < 128 := by have := (hz 0 (by decide)).1; omega
  have hF : ∀ m, m ≤ 8 → ∀ j, 32 * m ≤ j → j < 256 → (layF blk F 4 zi (4 * m))[j]! = F[j]! := fun m hm j h1 h2 => by
    rw [layF_get hblk F (by decide) zi (by omega) h2, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  refine ylay42_loop hY ht (fun m => 4 * m) rfl (fun m _ => by
      rw [show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 (2 * 4) by decide, wAddr_add,
        show t + 4 * m + 4 = t + 4 * (m + 1) by omega])
    (fun m => layF blk F 4 zi (4 * m)) (fun m l e => zeta (zi (4 * m + l + 2 * (e / 4))))
    (fun m hm s' h8 hT' hw' => WP.mono (yzetaS_ok 0xA0 0xF5 (zP := sP) (z := z) (k := t + 4 * m)
        (fun j hj => by rw [sel_A0 hj]; have := (hz (4 * m + 3) (by omega)).1; omega)
        (fun j hj => by rw [sel_F5 hj]; have := (hz (4 * m + 3) (by omega)).1; omega) h8
        (tab_in (List.mem_append_right _ hw') (by omega)) hT')
      fun s'' ⟨Z0, Z1, o⟩ => ⟨fun l hl => ?_, o.mono (by simp)⟩) (fun m hm l hl t' hc' hA hB hZ => ?_) ?_ hc hsi
    hS hT hw
  · rcases lane01 hl with rfl | rfl
    · exact Z0.congr fun i hi => by
        rw [sel_A0 (by omega), show t + 4 * m + 2 * (i / 2 / 2) = t + (4 * m + 0 + 2 * (i / 4)) by omega,
          (hz _ (by omega)).2]
    · exact Z1.congr fun i hi => by
        rw [sel_F5 (by omega), show t + 4 * m + (1 + 2 * (i / 2 / 2)) = t + (4 * m + 1 + 2 * (i / 4)) by omega,
          (hz _ (by omega)).2]
  · refine WP.mono (core4_ok hbf hc' hA hB hZ) fun t'' ⟨⟨a, b⟩, o⟩ => ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
    · have hR := layF_get hblk F (len := 4) (by decide) zi (b := 4 * (m + 1)) (by omega) (show 32 * m + 8 * l + e < 256 by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 32 * m + 8 * l + e < 2 * 4 * (4 * (m + 1)) by omega)),
        show (32 * m + 8 * l + e) / (2 * 4) = 4 * m + l by omega] at hR
      rw [hR]
      by_cases h : e < 4
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
          ite_eq_left_of_eq_true _ _ (eq_true (show (32 * m + 8 * l + e) % (2 * 4) < 4 by omega)),
          hF m (by omega) (32 * m + 8 * l + e) (by omega) (by omega),
          hF m (by omega) (32 * m + 8 * l + (4 + e)) (by omega) (by omega),
          show 32 * m + 8 * l + (4 + e) = 32 * m + 8 * l + e + 4 by omega, show 4 * m + l + 2 * (e / 4) = 4 * m + l by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (32 * m + 8 * l + e) % (2 * 4) < 4 by omega)),
          hF m (by omega) (32 * m + 8 * l + (e - 4)) (by omega) (by omega),
          hF m (by omega) (32 * m + 8 * l + e) (by omega) (by omega),
          show 32 * m + 8 * l + (e - 4) = 32 * m + 8 * l + e - 4 by omega,
          show 4 * m + l + 2 * ((e - 4) / 4) = 4 * m + l by omega]
    · have hR := layF_get hblk F (len := 4) (by decide) zi (b := 4 * (m + 1)) (by omega)
        (show 32 * m + 16 + 8 * l + e < 256 by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 32 * m + 16 + 8 * l + e < 2 * 4 * (4 * (m + 1)) by omega)),
        show (32 * m + 16 + 8 * l + e) / (2 * 4) = 4 * m + l + 2 by omega] at hR
      rw [hR]
      by_cases h : e < 4
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
          ite_eq_left_of_eq_true _ _ (eq_true (show (32 * m + 16 + 8 * l + e) % (2 * 4) < 4 by omega)),
          hF m (by omega) (32 * m + 16 + 8 * l + e) (by omega) (by omega),
          hF m (by omega) (32 * m + 16 + 8 * l + (4 + e)) (by omega) (by omega),
          show 32 * m + 16 + 8 * l + (4 + e) = 32 * m + 16 + 8 * l + e + 4 by omega,
          show 4 * m + l + 2 * ((4 + e) / 4) = 4 * m + l + 2 by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (32 * m + 16 + 8 * l + e) % (2 * 4) < 4 by omega)),
          hF m (by omega) (32 * m + 16 + 8 * l + (e - 4)) (by omega) (by omega),
          hF m (by omega) (32 * m + 16 + 8 * l + e) (by omega) (by omega),
          show 32 * m + 16 + 8 * l + (e - 4) = 32 * m + 16 + 8 * l + e - 4 by omega,
          show 4 * m + l + 2 * (e / 4) = 4 * m + l + 2 by omega]
  · intro m hm i hi h
    rw [layF_get hblk F (by decide) zi (by omega) hi, layF_get hblk F (by decide) zi (by omega) hi]
    rcases h with h | h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 4 * (4 * (m + 1)) by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 4 * (4 * m) by omega))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 4 * (4 * (m + 1)) by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 4 * (4 * m) by omega))]

theorem ylay2_ok (hY : laneSseBlock (toY (gath2 ++ bf ++ scat2)) = some (gath2 ++ bf ++ scat2))
    {sP : Addr} {t : Nat} (zi : Nat → Nat) {z : Nat → Zq}
    (hz : ∀ c < 64, t + c < 128 ∧ z (t + c) = zeta (zi c))
    {F : Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 bf t) s fun s' => S16 s'.mem (spW sP) (layF blk F 2 zi 64) ∧ BInvY sP s s' := by
  have ht : t < 128 := by have := (hz 0 (by decide)).1; omega
  have hF : ∀ m, m ≤ 8 → ∀ j, 32 * m ≤ j → j < 256 → (layF blk F 2 zi (8 * m))[j]! = F[j]! := fun m hm j h1 h2 => by
    rw [layF_get hblk F (by decide) zi (by omega) h2, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  refine ylay42_loop hY ht (fun m => 8 * m) rfl (fun m _ => by
      rw [show BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 (2 * 8) by decide, wAddr_add,
        show t + 8 * m + 8 = t + 8 * (m + 1) by omega])
    (fun m => layF blk F 2 zi (8 * m)) (fun m l e => zeta (zi (8 * m + (2 * l + e / 2 + 2 * (e / 4)))))
    (fun m hm s' h8 hT' hw' => WP.mono (yzeta8_ok (zP := sP) (z := z) (k := t + 8 * m)
        (by have := (hz (8 * m + 7) (by omega)).1; omega) h8 (tab_in (List.mem_append_right _ hw') (by omega)) hT')
      fun s'' ⟨Z, o⟩ => ⟨fun l hl => (Z l hl).congr fun i hi => by
        rw [Nat.add_assoc, (hz _ (by omega)).2], o.mono (by simp)⟩)
    (fun m hm l hl t' hc' hA hB hZ => ?_) ?_ hc hsi hS hT hw
  · refine WP.mono (core2_ok hbf hc' hA hB hZ) fun t'' ⟨⟨a, b⟩, o⟩ => ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
    · have hR := layF_get hblk F (len := 2) (by decide) zi (b := 8 * (m + 1)) (by omega)
        (show 32 * m + 8 * l + e < 256 by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 32 * m + 8 * l + e < 2 * 2 * (8 * (m + 1)) by omega)),
        show (32 * m + 8 * l + e) / (2 * 2) = 8 * m + (2 * l + (2 * (e / 4) + e % 2) / 2 +
          2 * ((2 * (e / 4) + e % 2) / 4)) by omega] at hR
      rw [hR]
      by_cases h : e % 4 < 2
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
          ite_eq_left_of_eq_true _ _ (eq_true (show (32 * m + 8 * l + e) % (2 * 2) < 2 by omega)),
          hF m (by omega) (32 * m + 8 * l + e) (by omega) (by omega),
          hF m (by omega) (32 * m + 8 * l + (e + 2)) (by omega) (by omega),
          show 32 * m + 8 * l + (e + 2) = 32 * m + 8 * l + e + 2 by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (32 * m + 8 * l + e) % (2 * 2) < 2 by omega)),
          hF m (by omega) (32 * m + 8 * l + (e - 2)) (by omega) (by omega),
          hF m (by omega) (32 * m + 8 * l + e) (by omega) (by omega),
          show 32 * m + 8 * l + (e - 2) = 32 * m + 8 * l + e - 2 by omega]
    · have hR := layF_get hblk F (len := 2) (by decide) zi (b := 8 * (m + 1)) (by omega)
        (show 32 * m + 16 + 8 * l + e < 256 by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 32 * m + 16 + 8 * l + e < 2 * 2 * (8 * (m + 1)) by omega)),
        show (32 * m + 16 + 8 * l + e) / (2 * 2) = 8 * m + (2 * l + (4 + 2 * (e / 4) + e % 2) / 2 +
          2 * ((4 + 2 * (e / 4) + e % 2) / 4)) by omega] at hR
      rw [hR]
      by_cases h : e % 4 < 2
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
          ite_eq_left_of_eq_true _ _ (eq_true (show (32 * m + 16 + 8 * l + e) % (2 * 2) < 2 by omega)),
          hF m (by omega) (32 * m + 16 + 8 * l + e) (by omega) (by omega),
          hF m (by omega) (32 * m + 16 + 8 * l + (e + 2)) (by omega) (by omega),
          show 32 * m + 16 + 8 * l + (e + 2) = 32 * m + 16 + 8 * l + e + 2 by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (32 * m + 16 + 8 * l + e) % (2 * 2) < 2 by omega)),
          hF m (by omega) (32 * m + 16 + 8 * l + (e - 2)) (by omega) (by omega),
          hF m (by omega) (32 * m + 16 + 8 * l + e) (by omega) (by omega),
          show 32 * m + 16 + 8 * l + (e - 2) = 32 * m + 16 + 8 * l + e - 2 by omega]
  · intro m hm i hi h
    rw [layF_get hblk F (by decide) zi (by omega) hi, layF_get hblk F (by decide) zi (by omega) hi]
    rcases h with h | h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 2 * (8 * (m + 1)) by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 2 * (8 * m) by omega))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 2 * (8 * (m + 1)) by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 2 * (8 * m) by omega))]

end

end VG.Proof.MlKem.X86_64