import VerifiedGarbage.Proof.MlKem.X86_64.YNtt

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse with `len ≥ 8` on AVX2 registers

For any butterfly code `bf` that does what `op` does to the words of two SSE
registers (`VBflyOk`) and whose AVX2 form does it in each lane (`laneSseBlock
(toY bf) = some bf`), and any block of the specification whose butterflies do
`op` (`BlkOk`): sixteen butterflies of a block (`ystep`), the `len / 16` of
them of a block (`yblock_ok`), and the `128 / len` blocks of a layer with `len
≥ 16` (`ylay_ok`); and the layer with `len = 8`, two blocks at a time
(`ylay8_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The facts a piece of a layer keeps. -/
structure BInvY (sP : Addr) (s₀ s : State) : Prop where
  keep : Keep [.r8, .rcx, .rdx, .rax] s₀ s
  frame : Frame [sR (spW sP)] s₀.mem s.mem
  consts : YConsts s
  mxcsr : s.mxcsr = s₀.mxcsr

theorem BInvY.trans {sP : Addr} {s₁ s₂ s₃ : State} (h₁ : BInvY sP s₁ s₂) (h₂ : BInvY sP s₂ s₃) : BInvY sP s₁ s₃ :=
  ⟨(h₁.keep.trans h₂.keep).mono (by simp), h₁.frame.trans h₂.frame, h₂.consts, h₂.mxcsr.trans h₁.mxcsr⟩

theorem sp_inY {rs : List Region} {sP : Addr} (hw : pR sP ∈ rs) {j : Nat} (hj : j + 16 ≤ 256) :
    InRegions rs (wAddr (spW sP) j) 32 := by
  refine ⟨_, hw, ?_⟩
  rw [wAddr, spW, Offset.add_add]
  exact Offset.contains_base sP (by omega) (by omega)

theorem lane_gpr {s s' : State} (h : ∀ r l, s'.lane r l = s.lane r l) {rs : List XReg} {s₀ : State}
    (o : YOnly rs s₀ s) {r : XReg} (hr : r ∉ rs) {l : Nat} (hl : l < 2) : s'.lane r l = s₀.lane r l := by
  rw [h, o.lane r hr l hl]

/-- `GOnly` keeps the lanes of the vector registers if it keeps their upper halves. -/
theorem GOnly.lane {rs : List Reg} {s s' : State} (h : GOnly rs s s') (hy : s'.ymmHi = s.ymmHi) (r : XReg) (l : Nat) :
    s'.lane r l = s.lane r l := by
  simp only [State.lane]; rw [h.xmm, hy]

theorem Lanes.congr {x : BitVec 128} {f g : Nat → Zq} (h : Lanes x f) (e : ∀ i < 8, f i = g i) : Lanes x g :=
  fun i hi => by rw [h i hi, e i hi]

theorem ZLanes.congr {x : BitVec 128} {f g : Nat → Zq} (h : ZLanes x f) (e : ∀ i < 8, f i = g i) : ZLanes x g :=
  fun i hi => by rw [h i hi, e i hi]

/-- `add r, v`. -/
theorem addR_ok (r : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block [.alu .add r (.imm v)]) s fun s' =>
      s'.gpr r = s.gpr r + BitVec.signExtend 64 v ∧ GOnly [r] s s' ∧ s'.ymmHi = s.ymmHi := by
  vrunm [RegUpd.ymmHi_setReg]
  exact ⟨by gonly, rfl⟩

theorem sel_55 {j : Nat} (hj : j < 4) : sel 0x55 j = 1 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  (hY : laneSseBlock (toY bf) = some bf)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hY

/-- The butterflies of `bf` in each lane, from the words `x` and `y` of the
lanes of `ymm0` and `ymm1` and the zetas `ζ` of those of `ymm13`. -/
theorem ybf_ok {s : State} (hc : YConsts s) {x y ζ : Nat → Nat → Zq} (hx : ∀ l < 2, Lanes (s.lane .xmm0 l) (x l))
    (hy : ∀ l < 2, Lanes (s.lane .xmm1 l) (y l)) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (ζ l)) :
    WP isa (.block (toY bf)) s fun s' =>
      (∀ l < 2, Lanes (s'.lane .xmm0 l) (fun i => (op (x l i) (y l i) (ζ l i)).1) ∧
        Lanes (s'.lane .xmm3 l) (fun i => (op (x l i) (y l i) (ζ l i)).2)) ∧
      YOnly [.xmm1, .xmm2, .xmm0, .xmm3] s s' :=
  ylanes hY (P := fun l t => Lanes (t.xmm .xmm0) (fun i => (op (x l i) (y l i) (ζ l i)).1) ∧
      Lanes (t.xmm .xmm3) (fun i => (op (x l i) (y l i) (ζ l i)).2))
    fun l hl => WP.mono (hbf _ (hc l hl) _ _ _ (hx l hl) (hy l hl) (hz l hl)) fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩

include hblk

/-- The body of the loop over the vectors of a block. -/
abbrev ybody (bf : List Instr) (len : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm1 (at_ .rdx (2 * len))] ++ toY bf ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx (2 * len)) .xmm3,
      .alu .add .rdx (.imm 32)] ++ [.alu .sub .rcx (.imm 1)]

theorem ystep {Sp : Addr} {len st u k : Nat} (hl : 16 ≤ len) (hl' : len ≤ 128) (hs : st + 2 * len ≤ 256)
    (hu : 16 * u + 16 ≤ len) {G : Poly} {s : State} (hc : YConsts s)
    (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun _ => zeta k))
    (hdx : s.gpr .rdx = wAddr Sp (st + 16 * u)) (hS : S16 s.mem Sp (blk G len k st (16 * u)))
    (hin : ∀ j, j + 16 ≤ 256 → InRegions s.wr (wAddr Sp j) 32) :
    WP isa (.block (ybody bf len)) s fun s' =>
      S16 s'.mem Sp (blk G len k st (16 * (u + 1))) ∧ s'.gpr .rdx = wAddr Sp (st + 16 * (u + 1)) ∧
        Frame [sR Sp] s.mem s'.mem ∧ YConsts s' ∧ (∀ l < 2, s'.lane .xmm13 l = s.lane .xmm13 l) ∧
        Keep [.rdx, .rcx] s s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        s'.mxcsr = s.mxcsr := by
  have j0 : st + 16 * u + 16 ≤ 256 := by omega
  have j1 : st + 16 * u + len + 16 ≤ 256 := by omega
  have a1 : wAddr Sp (st + 16 * u) + BitVec.ofNat 64 (2 * len) = wAddr Sp (st + 16 * u + len) := wAddr_add _ _ _
  have r0 : InRegions (s.rd ++ s.wr) (wAddr Sp (st + 16 * u) + BitVec.ofNat 64 0) 32 := by
    obtain ⟨r, hr, hc⟩ := hin _ j0; exact ⟨r, List.mem_append_right _ hr, by rw [add_ofNat_zero]; exact hc⟩
  have r1 : InRegions (s.rd ++ s.wr) (wAddr Sp (st + 16 * u) + BitVec.ofNat 64 (2 * len)) 32 := by
    obtain ⟨r, hr, hc⟩ := hin _ j1; exact ⟨r, List.mem_append_right _ hr, by rw [a1]; exact hc⟩
  rw [ybody, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [hdx]; exact r0)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, hdx]; exact r1)) fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  have o12 := o1.trans o2
  generalize hP : blk G len k st (16 * u) = P at hS
  refine WP.mono (ybf_ok hbf hY (o12.consts hc (by decide) (by decide))
    (x := fun l e => P[st + 16 * u + 8 * l + e]!) (y := fun l e => P[st + 16 * u + len + 8 * l + e]!)
    (ζ := fun _ _ => zeta k)
    (fun l hl => by
      rw [o2.lane _ (by decide) l hl, L1 l hl, hdx, add_ofNat_zero]; exact lanes_loadY hS j0 hl)
    (fun l hl => by
      rw [L2 l hl, o1.gpr, o1.mem, hdx, a1]; exact lanes_loadY hS j1 hl)
    (fun l hl => by rw [o12.lane _ (by decide) l hl]; exact hz l hl)) fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o12.trans o3
  have w0 : InRegions s3.wr (s3.gpr .rdx) 32 := by rw [o13.wr, o13.gpr, hdx]; exact hin _ j0
  have w1 : InRegions s3.wr (s3.gpr .rdx + BitVec.ofNat 64 (2 * len)) 32 := by
    rw [o13.wr, o13.gpr, hdx, a1]; exact hin _ j1
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1, sx32]
  have g3 : s3.gpr .rdx = wAddr Sp (st + 16 * u) := by rw [o13.gpr, hdx]
  rw [g3, a1, o13.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine s16_write2Y (s := s3) hS j0 j1 (by omega)
      (a := fun e => (op P[st + 16 * u + e]! P[st + 16 * u + len + e]! (zeta k)).1)
      (b := fun e => (op P[st + 16 * u + e]! P[st + 16 * u + len + e]! (zeta k)).2)
      (fun l hl i hi => by
        rw [(B3 l hl).1 i hi]; dsimp only
        rw [show st + 16 * u + 8 * l + i = st + 16 * u + (8 * l + i) by omega,
          show st + 16 * u + len + 8 * l + i = st + 16 * u + len + (8 * l + i) by omega])
      (fun l hl i hi => by
        rw [(B3 l hl).2 i hi]; dsimp only
        rw [show st + 16 * u + 8 * l + i = st + 16 * u + (8 * l + i) by omega,
          show st + 16 * u + len + 8 * l + i = st + 16 * u + len + (8 * l + i) by omega]) fun i hi => ?_
    rw [← hP, show 16 * (u + 1) = 16 * u + 16 by omega, hblk.add, hblk.get _ _ _ _ _ (by omega) (by omega)
      (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    rw [hP]
    by_cases c1 : st + 16 * u ≤ i ∧ i < st + 16 * u + 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c1), ite_eq_left_of_eq_true _ _ (eq_true c1),
        show st + 16 * u + (i - (st + 16 * u)) = i by omega,
        show st + 16 * u + len + (i - (st + 16 * u)) = i + len by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c1), ite_eq_right_of_eq_false _ _ (eq_false c1)]
      by_cases c2 : st + 16 * u + len ≤ i ∧ i < st + 16 * u + len + 16
      · rw [ite_eq_left_of_eq_true _ _ (eq_true c2), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
          show st + 16 * u + (i - (st + 16 * u + len)) = i - len by omega,
          show st + 16 * u + len + (i - (st + 16 * u + len)) = i by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false c2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add,
      show st + 16 * u + 16 = st + 16 * (u + 1) by omega]
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact lanes_gpr (s := s3) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o13 hc
      (by decide) (by decide)
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o13.lane _ (by decide) l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [o13.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr]
  · rw [o13.gpr]
  · rw [o13.gpr]
  · exact o13.mxcsr

/-- The code of a block of a layer with `len ≥ 16`. -/
abbrev yblk (bf : List Instr) (len : Nat) : Prog isa :=
  .seq (.block (yzeta1 ++ [.alu .add .r8 (.imm 2)]))
    (.seq (rcxLoop (len / 16) ([.vmovdquLoad .l256 .xmm0 (at_ .rdx 0),
        .vmovdquLoad .l256 .xmm1 (at_ .rdx (2 * len))] ++ toY bf ++
        [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx (2 * len)) .xmm3,
          .alu .add .rdx (.imm 32)]))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (2 * len))), .alu .sub .rax (.imm 1)]))

theorem yblock_ok {sP : Addr} {len st kz k : Nat} (h16 : 16 ≤ len) (hl16 : len % 16 = 0) (hl : len ≤ 128)
    (hs : st + 2 * len ≤ 256) (hkz : kz < 128) {z : Nat → Zq} (hzk : z kz = zeta k) {G : Poly} {s : State}
    (hc : YConsts s) (hdx : s.gpr .rdx = wAddr (spW sP) st) (h8r : s.gpr .r8 = wAddr sP kz)
    (hS : S16 s.mem (spW sP) G) (hT : TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (yblk bf len) s fun s' => S16 s'.mem (spW sP) (blk G len k st len) ∧
      s'.gpr .rdx = wAddr (spW sP) (st + 2 * len) ∧ s'.gpr .r8 = wAddr sP (kz + 1) ∧
      s'.gpr .rax = s.gpr .rax - 1 ∧ s'.zf = some (s.gpr .rax - 1 == 0) ∧ BInvY sP s s' := by
  -- the zeta
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (yzeta1_ok hkz h8r (tab_in (List.mem_append_right _ hw) (by omega)) hT) fun s1 ⟨z1, o1⟩ => ?_
  have g1 : s1.gpr = s.gpr := o1.gpr
  refine WP.mono (Q := fun (s2 : State) => s2.gpr .r8 = wAddr sP (kz + 1) ∧ GOnly [.r8] s1 s2 ∧ s2.ymmHi = s1.ymmHi)
    (by
      vrunm [g1, h8r, RegUpd.ymmHi_setReg]
      refine ⟨?_, by gonly, rfl⟩
      rw [show BitVec.signExtend 64 (2 : BitVec 32) = BitVec.ofNat 64 (2 * 1) from rfl, wAddr_add])
    fun s2 ⟨h82, o2, y2⟩ => ?_
  have l2 := GOnly.lane o2 y2
  have c2 : YConsts s2 := lanes_gpr (s := s1) l2 o1 hc (by decide) (by decide)
  have z2 : ∀ l < 2, ZLanes (s2.lane .xmm13 l) (fun _ => zeta k) := fun l hl => by
    rw [l2]; intro i hi; rw [z1 l hl i hi, hzk]
  have dx2 : s2.gpr .rdx = wAddr (spW sP) st := by rw [o2.keep.gpr (by decide), g1, hdx]
  have hw2 : pR sP ∈ s2.wr := by rw [o2.keep.2.2, o1.wr]; exact hw
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  refine WP.seq (WP.mono (wp_rcxLoopY (N := len / 16) (by omega) (by omega)
    (fun u w => S16 w.mem (spW sP) (blk G len k st (16 * u)) ∧ w.gpr .rdx = wAddr (spW sP) (st + 16 * u) ∧
      YConsts w ∧ (∀ l < 2, w.lane .xmm13 l = s2.lane .xmm13 l) ∧ Keep [.rcx, .rdx] s2 w ∧
      Frame [sR (spW sP)] s2.mem w.mem ∧ w.mxcsr = s2.mxcsr)
    (fun w o hy _ => ⟨by rw [hblk.zero, o.mem, m2]; exact hS, by rw [o.keep.gpr (by decide), dx2]; rfl,
      lanes_gpr (s := s2) (GOnly.lane o hy) (YOnly.refl [] s2) c2 (by decide) (by decide),
      fun l _ => GOnly.lane o hy _ l, o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun u hu w ⟨hS', hdx', hc', hz', hk', hf', hx'⟩ => WP.mono (ystep hbf hY hblk h16 hl hs (by
        have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hl16); omega) hc'
        (fun l hl => by rw [hz' l hl]; exact z2 l hl) hdx' hS'
        (fun j hj => sp_inY (by rw [hk'.2.2]; exact hw2) hj))
      fun w' ⟨hS'', hdx'', hf'', hc'', hz'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', fun l hl => by rw [hz'' l hl, hz' l hl], (hk'.trans hk'').mono (by simp),
          hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩)) fun w ⟨hS3, hdx3, hc3, _, hk3, hf3, hx3⟩ => ?_)
  rw [show 16 * (len / 16) = len from Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl16)] at hS3 hdx3
  have hax : w.gpr .rax = s.gpr .rax := by rw [hk3.gpr (by decide), o2.keep.gpr (by decide), g1]
  have h8w : w.gpr .r8 = wAddr sP (kz + 1) := by rw [hk3.gpr (by decide), h82]
  vrunm [hdx3, sx_ofNat (show 2 * len < 2 ^ 31 by omega), hax, h8w]
  refine ⟨hS3, by rw [wAddr_add, show st + len + len = st + 2 * len by omega], ?_⟩
  have k1 : Keep [.r8, .rcx, .rdx, .rax] s w :=
    (Keep.trans (⟨fun r _ => by rw [g1], o1.rd, o1.wr⟩ : Keep [] s s1) (o2.keep.trans hk3)).mono (by simp)
  refine ⟨⟨fun r hr => ?_, k1.2.1, k1.2.2⟩, by rw [← m2]; exact hf3,
    lanes_gpr (s := w) (fun r l => by simp only [lane_setReg, lane_setFlags]) (YOnly.refl [] w) hc3
      (by decide) (by decide),
    by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [hx3, o2.mxcsr, o1.mxcsr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  exact k1.gpr (by simp [hr])

/-! ## A layer with `len ≥ 16` -/

theorem ylay_ok {sP : Addr} {len t : Nat} (hlen : len ∈ [16, 32, 64, 128]) (zi : Nat → Nat) {z : Nat → Zq}
    (hzi : ∀ c < 128 / len, t + c < 128 ∧ z (t + c) = zeta (zi c))
    {F : Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay bf len t) s fun s' => S16 s'.mem (spW sP) (layF blk F len zi (128 / len)) ∧
      BInvY sP s s' := by
  have hl : 16 ≤ len ∧ len % 16 = 0 ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
      128 / len ≤ 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h16, hl16, hl128, hcov, hpos, h8⟩ := hl
  have ht : t < 128 := by have := (hzi 0 hpos).1; omega
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = spW sP ∧ w.gpr .r8 = wAddr sP t ∧
      w.gpr .rax = BitVec.ofNat 64 (128 / len) ∧ GOnly [.rdx, .r8, .rax] s w ∧ w.ymmHi = s.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), sx_ofNat (show 2 * t < 2 ^ 31 by omega), hsi,
        RegUpd.ymmHi_setReg, RegUpd.ymmHi_setFlags]
      refine ⟨?_, by gonly⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega) fun w ⟨hdx, h8r, hax, o, hy⟩ => ?_)
  have hw' : pR sP ∈ w.wr := by rw [o.keep.2.2]; exact hw
  have cw : YConsts w := lanes_gpr (s := s) (GOnly.lane o hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_countdown (cnt := .rax) (N := 128 / len) (by omega) hpos
    (fun c u => S16 u.mem (spW sP) (layF blk F len zi c) ∧ u.gpr .rdx = wAddr (spW sP) (2 * len * c) ∧
      u.gpr .r8 = wAddr sP (t + c) ∧ BInvY sP w u ∧ TZ u.mem sP z)
    (fun c hc u ⟨hS', hdx', h8', hb', hT'⟩ _ => ?_) (fun u h => h)
    ⟨by rw [o.mem]; exact hS, by rw [hdx, wAddr, Nat.mul_zero, Nat.mul_zero, add_ofNat_zero],
      by rw [h8r, Nat.add_zero], ⟨Keep.refl _ _, Frame.refl _ _, cw, rfl⟩, by rw [o.mem]; exact hT⟩ hax)
    fun u ⟨hS', _, _, hb', _⟩ => ⟨hS', ⟨(o.keep.trans hb'.keep).mono (by simp),
      by rw [← o.mem]; exact hb'.frame, hb'.consts, by rw [hb'.mxcsr, o.mxcsr]⟩⟩
  have hs : 2 * len * c + 2 * len ≤ 256 := by
    have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (yblock_ok hbf hY hblk h16 hl16 hl128 hs (hzi c hc).1 (hzi c hc).2 hb'.consts hdx' h8' hS' hT'
    (by rw [hb'.keep.2.2]; exact hw')) fun u' ⟨hS'', hdx'', h8'', hax'', hzf'', hb''⟩ =>
      ⟨⟨by rw [layF, foldl_range_succ]; exact hS'', by rw [hdx'', Nat.mul_succ],
        by rw [h8'', Nat.add_assoc], hb'.trans hb'', hT'.frame hb''.frame⟩, hax'', hzf''⟩

/-! ## The layer with `len = 8` -/

/-- The body of the layer with `len = 8`. -/
abbrev ybody8 (bf : List Instr) : List Instr :=
  [.vmovdquLoad .l256 .xmm4 (at_ .rdx 0)] ++ ([.vmovdquLoad .l256 .xmm5 (at_ .rdx 32)] ++ (yzeta2 ++
    ([.alu .add .r8 (.imm 4)] ++ ([.vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20)] ++
    ([.vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] ++ (toY bf ++ ([.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20)] ++
    ([.vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31)] ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm4, .vmovdquStore .l256 (at_ .rdx 32) .xmm5, .alu .add .rdx (.imm 64),
      .alu .sub .rcx (.imm 1)]))))))))

theorem ystep8 {sP : Addr} {m t : Nat} (hm : m < 8) (zi : Nat → Nat) {z : Nat → Zq}
    (hz : ∀ c < 16, t + c < 128 ∧ z (t + c) = zeta (zi c)) {F : Poly} {s : State} (hc : YConsts s)
    (hdx : s.gpr .rdx = wAddr (spW sP) (32 * m)) (h8 : s.gpr .r8 = wAddr sP (t + 2 * m))
    (hS : S16 s.mem (spW sP) (layF blk F 8 zi (2 * m))) (hT : TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (.block (ybody8 bf)) s fun s' =>
      S16 s'.mem (spW sP) (layF blk F 8 zi (2 * (m + 1))) ∧ s'.gpr .rdx = wAddr (spW sP) (32 * (m + 1)) ∧
      s'.gpr .r8 = wAddr sP (t + 2 * (m + 1)) ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInvY sP s s' := by
  have j0 : 32 * m + 16 ≤ 256 := by omega
  have j1 : 32 * m + 16 + 16 ≤ 256 := by omega
  have a1 : wAddr (spW sP) (32 * m) + BitVec.ofNat 64 32 = wAddr (spW sP) (32 * m + 16) := wAddr_add _ _ 16
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact sp_inY (List.mem_append_right s.rd hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [hdx, a1]; exact sp_inY (List.mem_append_right s.rd hw) j1
  generalize hP : layF blk F 8 zi (2 * m) = P at hS
  -- the loads
  rw [ybody8, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L4, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L5, o2⟩ => ?_
  have o12 := o1.trans o2
  -- the zetas
  rw [WP.block_append_iff]
  have hk0 := hz (2 * m) (by omega)
  have hk1 := hz (2 * m + 1) (by omega)
  refine WP.mono (yzetaS_ok 0x00 0x55 (zP := sP) (z := z) (k := t + 2 * m) (fun j _ => by rw [sel_zero]; omega)
    (fun j hj => by rw [sel_55 hj]; omega) (by rw [o12.gpr, h8])
    (by rw [o12.rd, o12.wr]; exact tab_in (List.mem_append_right _ hw) (by omega)) (by rw [o12.mem]; exact hT))
    fun s3 ⟨Z0, Z1, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addR_ok .r8 4 s3) fun s4 ⟨h84, g4, y4⟩ => ?_
  have l4 := GOnly.lane g4 y4
  -- the lower and upper halves
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s4) fun s5 ⟨P5, o5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s5) fun s6 ⟨P6, o6⟩ => ?_
  have c6 : YConsts s6 := (o5.trans o6).consts (lanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide))
    (by decide) (by decide)
  have m3 : s3.mem = s.mem := (o12.trans o3).mem
  have q4 : ∀ l < 2, s4.lane .xmm4 l = s.mem.readW (wAddr (spW sP) (32 * m) + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by rw [l4, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl, L4 l hl, hdx, add_ofNat_zero]
  have q5 : ∀ l < 2, s4.lane .xmm5 l = s.mem.readW (wAddr (spW sP) (32 * m + 16) + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by rw [l4, o3.lane _ (by decide) l hl, L5 l hl, o1.gpr, o1.mem, hdx, a1]
  rw [WP.block_append_iff]
  refine WP.mono (ybf_ok hbf hY c6 (x := fun l e => P[32 * m + 16 * l + e]!)
    (y := fun l e => P[32 * m + 16 * l + 8 + e]!) (ζ := fun l _ => zeta (zi (2 * m + l)))
    (fun l hl => by
      rw [o6.lane _ (by decide) l hl, P5 l hl, perm20 _ _ hl]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, q4 0 (by decide)]
        exact (lanes_loadY hS j0 (by decide)).congr fun e _ => rfl
      · rw [ifn (by decide), q5 0 (by decide)]
        exact (lanes_loadY hS j1 (by decide)).congr fun e _ => by congr 2)
    (fun l hl => by
      rw [P6 l hl, perm31 _ _ hl, o5.lane .xmm4 (by decide) 1 (by decide), o5.lane .xmm5 (by decide) 1 (by decide)]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, q4 1 (by decide)]
        exact (lanes_loadY hS j0 (by decide)).congr fun e _ => by congr 2
      · rw [ifn (by decide), q5 1 (by decide)]
        exact (lanes_loadY hS j1 (by decide)).congr fun e _ => by congr 2)
    (fun l hl => by
      rw [(o5.trans o6).lane _ (by decide) l hl, l4]
      rcases lane01 hl with rfl | rfl
      · exact Z0.congr fun i _ => by rw [sel_zero, Nat.add_zero, hk0.2, Nat.add_zero]
      · exact Z1.congr fun i hi => by rw [sel_55 (by omega), Nat.add_assoc, hk1.2]))
    fun s7 ⟨B7, o7⟩ => ?_
  -- the blocks back
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s7) fun s8 ⟨P8, o8⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s8) fun s9 ⟨P9, o9⟩ => ?_
  have o39 := (o5.trans o6).trans (o7.trans (o8.trans o9))
  have w0 : InRegions s9.wr (s9.gpr .rdx) 32 := by
    rw [o39.wr, o39.gpr, g4.keep.2.2, g4.keep.gpr (by decide), o3.wr, o3.gpr, o12.wr, o12.gpr, hdx]
    exact sp_inY hw j0
  have w1 : InRegions s9.wr (s9.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [o39.wr, o39.gpr, g4.keep.2.2, g4.keep.gpr (by decide), o3.wr, o3.gpr, o12.wr, o12.gpr, hdx, a1]
    exact sp_inY hw j1
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  have g9 : s9.gpr = s4.gpr := o39.gpr
  have m9 : s9.mem = s.mem := by rw [o39.mem, g4.mem, m3]
  have dx9 : s9.gpr .rdx = wAddr (spW sP) (32 * m) := by
    rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr, hdx]
  rw [dx9, a1, m9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · -- the words stored
    have v0 : ∀ l < 2, ∀ e < 8, (P[32 * m + 16 * l + e]! : Zq) = P[32 * m + 16 * l + e]! := fun _ _ _ _ => rfl
    refine s16_write2Y (s := s9) hS j0 j1 (by omega)
      (a := fun e => if e < 8 then (op P[32 * m + e]! P[32 * m + 8 + e]! (zeta (zi (2 * m)))).1
        else (op P[32 * m + (e - 8)]! P[32 * m + 8 + (e - 8)]! (zeta (zi (2 * m)))).2)
      (b := fun e => if e < 8 then (op P[32 * m + 16 + e]! P[32 * m + 16 + 8 + e]! (zeta (zi (2 * m + 1)))).1
        else (op P[32 * m + 16 + (e - 8)]! P[32 * m + 16 + 8 + (e - 8)]! (zeta (zi (2 * m + 1)))).2)
      (fun l hl i hi => ?_) (fun l hl i hi => ?_) (fun i hi => ?_)
    · rw [o9.lane .xmm4 (by decide) l hl, P8 l hl, perm20 _ _ hl]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, (B7 0 (by decide)).1 i hi]; dsimp only; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
        try simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      · rw [ifn (by decide), (B7 0 (by decide)).2 i hi]; dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show 8 * 1 + i - 8 = i by omega]
        try simp only [Nat.mul_zero, Nat.add_zero]
    · rw [P9 l hl, perm31 _ _ hl, o8.lane .xmm0 (by decide) 1 (by decide), o8.lane .xmm3 (by decide) 1 (by decide)]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, (B7 1 (by decide)).1 i hi]; dsimp only; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
        try simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
      · rw [ifn (by decide), (B7 1 (by decide)).2 i hi]; dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show 8 * 1 + i - 8 = i by omega]
        try simp only [Nat.mul_one]
    · -- the specification: two blocks
      rw [← hP, layF_get hblk F (by decide) zi (by omega) hi]
      have hF : ∀ j, 32 * m ≤ j → j < 256 → (layF blk F 8 zi (2 * m))[j]! = F[j]! := fun j h1 h2 => by
        rw [layF_get hblk F (by decide) zi (by omega) h2, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      by_cases h1 : 32 * m ≤ i ∧ i < 32 * m + 16
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h1),
          show i / (2 * 8) = 2 * m by omega]
        by_cases h2 : i - 32 * m < 8
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h2),
            hF _ (by omega) (by omega), hF _ (by omega) (by omega), show 32 * m + (i - 32 * m) = i by omega,
            show 32 * m + 8 + (i - 32 * m) = i + 8 by omega]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h2),
            hF _ (by omega) (by omega), hF _ (by omega) (by omega), show 32 * m + (i - 32 * m - 8) = i - 8 by omega,
            show 32 * m + 8 + (i - 32 * m - 8) = i by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        by_cases h1' : 32 * m + 16 ≤ i ∧ i < 32 * m + 16 + 16
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h1'),
            show i / (2 * 8) = 2 * m + 1 by omega]
          by_cases h2 : i - (32 * m + 16) < 8
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h2),
              hF _ (by omega) (by omega), hF _ (by omega) (by omega),
              show 32 * m + 16 + (i - (32 * m + 16)) = i by omega,
              show 32 * m + 16 + 8 + (i - (32 * m + 16)) = i + 8 by omega]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h2),
              hF _ (by omega) (by omega), hF _ (by omega) (by omega),
              show 32 * m + 16 + (i - (32 * m + 16) - 8) = i - 8 by omega,
              show 32 * m + 16 + 8 + (i - (32 * m + 16) - 8) = i by omega]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h1'), layF_get hblk F (by decide) zi (b := 2 * m) (by omega) hi]
          by_cases h3 : i < 32 * m
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 8 * (2 * (m + 1)) by omega)),
              ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 8 * (2 * m) by omega))]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 8 * (2 * (m + 1)) by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 8 * (2 * m) by omega))]
  · rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) by decide, wAddr_add, Nat.mul_succ]
  · have e3 : s3.gpr .r8 = wAddr sP (t + 2 * m) := by rw [o3.gpr, o12.gpr, h8]
    try simp only [g9, h84]
    rw [e3, show BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 (2 * 2) by decide, wAddr_add,
      show t + 2 * m + 2 = t + 2 * (m + 1) by omega]
  · rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, State.setMem_gpr]
    rw [g9, g4.keep.gpr (by simp [hr]), o3.gpr, o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]
    rw [o39.rd, g4.keep.2.1, o3.rd, o12.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]
    rw [o39.wr, g4.keep.2.2, o3.wr, o12.wr]
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact lanes_gpr (s := s9) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane])
      o39 (lanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide)) (by decide) (by decide)
  · exact (o39.mxcsr.trans (g4.mxcsr.trans ((o12.trans o3).mxcsr)))

omit hbf hY hblk in
/-- The prologue of the layers with `len` = 8, 4 and 2. -/
theorem ypre_ok {sP : Addr} (t : Nat) (ht : t < 128) {s : State} (hsi : s.gpr .rsi = sP) :
    WP isa (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * t))) s fun w =>
      w.gpr .rdx = spW sP ∧ w.gpr .r8 = wAddr sP t ∧ GOnly [.rdx, .r8] s w ∧ w.ymmHi = s.ymmHi := by
  simp only [leaR, oS]
  vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), sx_ofNat (show 2 * t < 2 ^ 31 by omega), hsi,
    RegUpd.ymmHi_setReg]
  exact ⟨by gonly, rfl⟩

theorem ylay8_ok {sP : Addr} {t : Nat} (zi : Nat → Nat) {z : Nat → Zq}
    (hz : ∀ c < 16, t + c < 128 ∧ z (t + c) = zeta (zi c))
    {F : Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay8 bf t) s fun s' => S16 s'.mem (spW sP) (layF blk F 8 zi 16) ∧ BInvY sP s s' := by
  have ht : t < 128 := by have := (hz 0 (by decide)).1; omega
  refine WP.seq (WP.mono (ypre_ok t ht hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := lanes_gpr (s := s) (GOnly.lane og hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide)
    (fun i u => S16 u.mem (spW sP) (layF blk F 8 zi (2 * i)) ∧ u.gpr .rdx = wAddr (spW sP) (32 * i) ∧
      u.gpr .r8 = wAddr sP (t + 2 * i) ∧ BInvY sP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, wAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, Nat.mul_zero, Nat.add_zero], ⟨ou.keep.mono (by simp),
        by rw [ou.mem]; exact Frame.refl _ _,
        lanes_gpr (s := w) (GOnly.lane ou hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : TZ u.mem sP z := (by rw [og.mem]; exact hT : TZ w.mem sP z).frame hb'.frame
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [.vmovdquLoad .l256 .xmm4 (at_ .rdx 0), .vmovdquLoad .l256 .xmm5 (at_ .rdx 32)] ++ yzeta2 ++
      [.alu .add .r8 (.imm 4), .vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20), .vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] ++
      toY bf ++ [.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20), .vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31),
        .vmovdquStore .l256 (at_ .rdx 0) .xmm4, .vmovdquStore .l256 (at_ .rdx 32) .xmm5, .alu .add .rdx (.imm 64)] ++
      [.alu .sub .rcx (.imm 1)] = ybody8 bf by simp [List.append_assoc]]
  exact WP.mono (ystep8 hbf hY hblk hi zi hz hb'.consts hdx' h8' hS' hT' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', h8'', hb'.trans hb''⟩, hcx, hzf⟩

end

end VG.Proof.MlKem.X86_64
