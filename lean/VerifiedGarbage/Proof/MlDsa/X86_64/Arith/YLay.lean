import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay

/-!
# ML-DSA on x86-64: the layers of the NTT and its inverse with `len ≥ 4` on AVX2 registers

For any butterfly code `bf` that does what `op` does to the doublewords of two
SSE registers (`VBflyOk`) and whose AVX2 form does it in each lane
(`laneSseBlock (toY bf) = some bf`), and any block of the specification whose
butterflies do `op` (`BlkOk`): eight butterflies of a block (`ystep`), the
`len / 8` of them of a block (`yblock_ok`), and the `128 / len` blocks of a
layer with `len ≥ 8` (`ylay_ok`); and the layer with `len = 4`, two blocks at
a time, the lower halves of their coefficients gathered into `ymm0` and the
upper ones into `ymm1` by `vperm2i128` (`ylay4_ok`). The zetas: `yzeta1_ok`
and `yzetaS_ok`, and the layers' result coefficient by coefficient
(`layF_get`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok ifp ifn sel sel_lt sel_zero sel_55
  add_ofNat_zero GOnly addR_ok wp_rcxLoopY wp_countdown ybcast_ok yblend_ok yperm_ok perm20 perm31
  wp_cons_iff lane_setReg lane_setFlags State.setMem_ymm State.setMem_setMem sx32)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt PolyIs zetas)

/-! ## A layer, coefficient by coefficient -/

section
variable {op : Zq → Zq → Zq → Zq × Zq} {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hblk

/-- Each coefficient after the first `b` blocks of the layer with `len`. -/
theorem layF_get (F : Poly) {len : Nat} (hl : 0 < len) (zi : Nat → Nat) {b : Nat} (hb : 2 * len * b ≤ 256)
    {j : Nat} (hj : j < 256) :
    (layF blk F len zi b)[j]! = if j < 2 * len * b then
      (if j % (2 * len) < len then (op F[j]! F[j + len]! (zetas (zi (j / (2 * len))))).1
        else (op F[j - len]! F[j]! (zetas (zi (j / (2 * len))))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by omega)]; rfl
  | succ b ih =>
    have hb' : 2 * len * b + 2 * len ≤ 256 := by rw [Nat.mul_succ] at hb; exact hb
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ len _ _ len hl (Nat.le_refl _) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    have hd : ∀ i, 2 * len * b ≤ i → i < 2 * len * b + 2 * len → i / (2 * len) = b ∧
        i % (2 * len) = i - 2 * len * b := fun i h1 h2 => by
      have e1 : i / (2 * len) = b := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]; exact h1
        · rw [Nat.succ_mul, Nat.mul_comm b]; exact h2
      refine ⟨e1, ?_⟩
      have := Nat.div_add_mod i (2 * len)
      rw [e1] at this; omega
    by_cases h1 : 2 * len * b ≤ j ∧ j < 2 * len * b + len
    · obtain ⟨d1, d2⟩ := hd j h1.1 (by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ih (by omega) hj, ih (by omega) (by omega), d1,
        ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show j % (2 * len) < len by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j + len < 2 * len * b by omega))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : 2 * len * b + len ≤ j ∧ j < 2 * len * b + len + len
      · obtain ⟨d1, d2⟩ := hd j (by omega) (by omega)
        rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ih (by omega) (by omega), ih (by omega) hj, d1,
          ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j % (2 * len) < len by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j - len < 2 * len * b by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ih (by omega) hj]
        by_cases h3 : j < 2 * len * b
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h3),
            ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h3),
            ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]

end

/-! ## Coefficients in both lanes -/

/-- The facts a piece of a layer keeps. -/
structure BInvY (fP : Addr) (s₀ s : State) : Prop where
  keep : Keep [.r8, .rcx, .rdx, .rax] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem
  consts : YConsts s
  mxcsr : s.mxcsr = s₀.mxcsr

theorem BInvY.trans {fP : Addr} {s₁ s₂ s₃ : State} (h₁ : BInvY fP s₁ s₂) (h₂ : BInvY fP s₂ s₃) :
    BInvY fP s₁ s₃ :=
  ⟨(h₁.keep.trans h₂.keep).mono (by simp), h₁.frame.trans h₂.frame, h₂.consts, h₂.mxcsr.trans h₁.mxcsr⟩

/-- `YConsts` after code that changed the vector registers `rs` only, then
nothing in them. -/
theorem ylanes_gpr {s s' : State} (h : ∀ r l, s'.lane r l = s.lane r l) {rs : List XReg} {s₀ : State}
    (o : YOnly rs s₀ s) (hc : YConsts s₀) (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : YConsts s' :=
  fun l hl => ⟨by rw [State.proj_xmm, h]; exact (yonly_yconsts o hc h14 h15 l hl).q,
    by rw [State.proj_xmm, h]; exact (yonly_yconsts o hc h14 h15 l hl).qinv⟩

/-- Two registers stored into a polynomial at coefficients `j` and `j'`,
lane `l` of each holding the four coefficients of `R` from `j + 4l` and
`j' + 4l`. -/
theorem polyIs_write2L {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P) {j j' : Nat}
    (hj : j + 8 ≤ 256) (hj' : j' + 8 ≤ 256) (hsep : j + 8 ≤ j' ∨ j' + 8 ≤ j) {s : State} {x y : XReg}
    (hx : ∀ l < 2, DLanes (s.lane x l) (fun e => R[j + 4 * l + e]!))
    (hy : ∀ l < 2, DLanes (s.lane y l) (fun e => R[j' + 4 * l + e]!))
    (hR : ∀ i < 256, (i < j ∨ j + 8 ≤ i) → (i < j' ∨ j' + 8 ≤ i) → R[i]! = P[i]!) :
    PolyIs ((m.writeW (coeffAddr p j) (s.ymm x)).writeW (coeffAddr p j') (s.ymm y)) p R :=
  polyIs_write2Y hP hj hj' hsep (a := fun e => R[j + e]!) (b := fun e => R[j' + e]!)
    (ylanes_ymm (fun e he => (hx 0 (by decide) e he).trans (by simp only [Nat.mul_zero, Nat.add_zero]))
      (fun e he => (hx 1 (by decide) e he).trans (by dsimp only; rw [show j + 4 * 1 + e = j + (e + 4) by omega])))
    (ylanes_ymm (fun e he => (hy 0 (by decide) e he).trans (by simp only [Nat.mul_zero, Nat.add_zero]))
      (fun e he => (hy 1 (by decide) e he).trans (by dsimp only; rw [show j' + 4 * 1 + e = j' + (e + 4) by omega])))
    fun i hi => by
      by_cases h1 : j ≤ i ∧ i < j + 8
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), show j + (i - j) = i by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        by_cases h2 : j' ≤ i ∧ i < j' + 8
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), show j' + (i - j') = i by omega]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]; exact hR i hi (by omega) (by omega)

theorem DLanes.congr {x : BitVec 128} {f g : Nat → Zq} (h : DLanes x f) (e : ∀ i < 4, f i = g i) : DLanes x g :=
  fun i hi => by rw [h i hi, e i hi]

theorem ZLanes.congr {x : BitVec 128} {f g : Nat → Zq} (h : ZLanes x f) (e : ∀ i < 4, f i = g i) : ZLanes x g :=
  fun i hi => by rw [h i hi, e i hi]

theorem getP_congr (P : Poly) {a b : Nat} (h : a = b) : P[a]! = P[b]! := h ▸ rfl

/-- A butterfly of the coefficients at `a` and `b` of `P` with the zeta of
index `zi c`, at other indices that are the same. -/
theorem op_idx (op : Zq → Zq → Zq → Zq × Zq) (P : Poly) (zi : Nat → Nat) {a b c a' b' c' : Nat} (ha : a = a')
    (hb : b = b') (hc : c = c') : op P[a]! P[b]! (zetas (zi c)) = op P[a']! P[b']! (zetas (zi c')) := by
  subst ha hb hc; rfl

/-- The prologue of the layers with `len` = 4, 2 and 1. -/
theorem ypre21 {fP sP : Addr} (k : Nat) (hk : k + 4 ≤ 256) {s : State} (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) :
    WP isa (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ leaR .r8 .rsi (4 * k))) s fun w =>
      w.gpr .rdx = fP ∧ w.gpr .r8 = coeffAddr sP k ∧ GOnly [.rdx, .r8] s w ∧ w.ymmHi = s.ymmHi := by
  simp only [leaR]
  vrund [sx_ofNat (show 4 * k < 2 ^ 31 by omega), hsi, hdi]
  exact ⟨by gonlyd, rfl⟩

/-! ## The zetas -/

theorem zodd_F5 (x : BitVec 128) : ZOdd x (shufDwords x 0xF5) := fun j hj => by
  rw [dword_shufDwords _ _ (by omega)]
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl

/-- The zetas `pshufd` with `o` leaves of the four at index `k` of the table. -/
theorem zlanes_tab (o : BitVec 8) {zP : Addr} {k : Nat} (hk : ∀ j < 4, k + sel o j < 256) {m : Mem}
    (ht : Tab zmTab m zP 256) :
    ZLanes (shufDwords (m.readW (coeffAddr zP k) 128) o) (fun i => zetas (k + sel o i)) := fun i hi => by
  have hs := sel_lt o i
  rw [dword_shufDwords_sel _ _ hi, dword_readW _ _ hs, coeffAddr_add]
  exact tab_zeta ht (hk i hi)

theorem zsse1_ok (t : State) :
    WP isa (.block [.xop (.pshufd .xmm13 .xmm13 0), .xop (.pshufd .xmm12 .xmm13 0xF5)]) t fun t' =>
      (t'.xmm .xmm13 = shufDwords (t.xmm .xmm13) 0 ∧
        t'.xmm .xmm12 = shufDwords (shufDwords (t.xmm .xmm13) 0) 0xF5) ∧ XOnly [.xmm13, .xmm12] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem yzeta1_ok {zP : Addr} {k : Nat} (hk : k + 4 ≤ 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 16) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block yzeta1) s fun s' => (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun _ => zetas k) ∧
      ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta1, wp_cons_iff]
  refine WP.mono (ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm13 = shufDwords (s1.lane .xmm13 l) 0 ∧
      t.xmm .xmm12 = shufDwords (shufDwords (s1.lane .xmm13 l) 0) 0xF5)
    fun l _ => zsse1_ok (s1.proj l)) fun s2 ⟨l2, o2⟩ => ⟨fun l hl => ?_, (o1.trans o2).mono (by simp)⟩
  have e13 : s2.lane .xmm13 l = _ := (l2 l hl).1
  have e12 : s2.lane .xmm12 l = _ := (l2 l hl).2
  rw [e12, e13, b1 l hl, h8, add_ofNat_zero]
  refine ⟨fun i hi => ?_, zodd_F5 _⟩
  rw [zlanes_tab 0 (fun j _ => by rw [sel_zero]; omega) ht i hi]
  dsimp only; rw [sel_zero, Nat.add_zero]

theorem zsseS_ok (o₀ o₁ : BitVec 8) (t : State) :
    WP isa (.block [.xop (.pshufd .xmm2 .xmm13 o₁), .xop (.pshufd .xmm13 .xmm13 o₀)]) t fun t' =>
      (t'.xmm .xmm13 = shufDwords (t.xmm .xmm13) o₀ ∧ t'.xmm .xmm2 = shufDwords (t.xmm .xmm13) o₁) ∧
        XOnly [.xmm2, .xmm13] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem zsseF5_ok (t : State) :
    WP isa (.block [.xop (.pshufd .xmm12 .xmm13 0xF5)]) t fun t' =>
      t'.xmm .xmm12 = shufDwords (t.xmm .xmm13) 0xF5 ∧ XOnly [.xmm12] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

/-- The odd zetas of each lane of `ymm13` in the even doublewords of `ymm12`. -/
theorem yF5_ok (s : State) :
    WP isa (.block (toY [.xop (.pshufd .xmm12 .xmm13 0xF5)])) s fun s' =>
      (∀ l < 2, s'.lane .xmm12 l = shufDwords (s.lane .xmm13 l) 0xF5) ∧ YOnly [.xmm12] s s' :=
  ylanes (by decide) (P := fun l t => t.xmm .xmm12 = shufDwords (s.lane .xmm13 l) 0xF5)
    fun l _ => zsseF5_ok (s.proj l)

theorem yzetaS_ok (o₀ o₁ : BitVec 8) {zP : Addr} {k : Nat} (hk0 : ∀ j < 4, k + sel o₀ j < 256)
    (hk1 : ∀ j < 4, k + sel o₁ j < 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 16) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block (yzetaS o₀ o₁)) s fun s' => ZLanes (s'.lane .xmm13 0) (fun i => zetas (k + sel o₀ i)) ∧
      ZLanes (s'.lane .xmm13 1) (fun i => zetas (k + sel o₁ i)) ∧
      (∀ l < 2, ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm2, .xmm12] s s' := by
  rw [yzetaS, WP.block_append_iff, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by rfl) (P := fun l t =>
      t.xmm .xmm13 = shufDwords (s1.lane .xmm13 l) o₀ ∧ t.xmm .xmm2 = shufDwords (s1.lane .xmm13 l) o₁)
    fun l _ => zsseS_ok o₀ o₁ (s1.proj l)) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (yblend_ok s2) fun s3 ⟨e0, e1, o3⟩ => ?_
  refine WP.mono (yF5_ok s3) fun s4 ⟨f4, o4⟩ => ?_
  have x0 : s4.lane .xmm13 0 = shufDwords (s.mem.readW (coeffAddr zP k) 128) o₀ := by
    have e : s2.lane .xmm13 0 = _ := (l2 0 (by decide)).1
    rw [o4.lane _ (by decide) 0 (by decide), e0, e, b1 0 (by decide), h8, add_ofNat_zero]
  have x1 : s4.lane .xmm13 1 = shufDwords (s.mem.readW (coeffAddr zP k) 128) o₁ := by
    have e : s2.lane .xmm2 1 = _ := (l2 1 (by decide)).2
    rw [o4.lane _ (by decide) 1 (by decide), e1, e, b1 1 (by decide), h8, add_ofNat_zero]
  refine ⟨by rw [x0]; exact zlanes_tab o₀ hk0 ht, by rw [x1]; exact zlanes_tab o₁ hk1 ht,
    fun l hl => ?_, (((o1.trans o2).trans o3).trans o4).mono (by simp)⟩
  rw [f4 l hl, o4.lane _ (by decide) l hl]
  exact zodd_F5 _

/-! ## A layer with `len ≥ 8` -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  (hY : laneSseBlock (toY bf) = some bf)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hY

/-- The butterflies of `bf` in each lane, from the coefficients `x` and `y`
of the lanes of `ymm0` and `ymm1` and the zetas `ζ` of those of `ymm13`. -/
theorem ybf_ok {s : State} (hc : YConsts s) {x y ζ : Nat → Nat → Zq}
    (hx : ∀ l < 2, DLanes (s.lane .xmm0 l) (x l)) (hy : ∀ l < 2, DLanes (s.lane .xmm1 l) (y l))
    (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (ζ l)) (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l)) :
    WP isa (.block (toY bf)) s fun s' =>
      (∀ l < 2, DLanes (s'.lane .xmm0 l) (fun i => (op (x l i) (y l i) (ζ l i)).1) ∧
        DLanes (s'.lane .xmm3 l) (fun i => (op (x l i) (y l i) (ζ l i)).2)) ∧
      YOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s' :=
  ylanes hY (P := fun l t => DLanes (t.xmm .xmm0) (fun i => (op (x l i) (y l i) (ζ l i)).1) ∧
      DLanes (t.xmm .xmm3) (fun i => (op (x l i) (y l i) (ζ l i)).2))
    fun l hl => WP.mono (hbf _ (hc l hl) _ _ _ (hx l hl) (hy l hl) (hz l hl) (ho l hl))
      fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩

include hblk

/-- The body of the loop over the vectors of a block. -/
abbrev ybody (bf : List Instr) (len : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm1 (at_ .rdx (4 * len))] ++ toY bf ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx (4 * len)) .xmm3,
      .alu .add .rdx (.imm 32)] ++ [.alu .sub .rcx (.imm 1)]

theorem ystep {fP : Addr} {len st u k : Nat} (hl : 8 ≤ len) (hs : st + 2 * len ≤ 256) (hu : 8 * u + 8 ≤ len)
    {G : Poly} {s : State} (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun _ => zetas k))
    (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l))
    (hdx : s.gpr .rdx = coeffAddr fP (st + 8 * u)) (hS : PolyIs s.mem fP (blk G len k st (8 * u)))
    (hw : pR fP ∈ s.wr) :
    WP isa (.block (ybody bf len)) s fun s' =>
      PolyIs s'.mem fP (blk G len k st (8 * (u + 1))) ∧ s'.gpr .rdx = coeffAddr fP (st + 8 * (u + 1)) ∧
        Frame [pR fP] s.mem s'.mem ∧ YConsts s' ∧ (∀ l < 2, s'.lane .xmm13 l = s.lane .xmm13 l) ∧
        (∀ l < 2, s'.lane .xmm12 l = s.lane .xmm12 l) ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : st + 8 * u + 8 ≤ 256 := by omega
  have j1 : st + 8 * u + len + 8 ≤ 256 := by omega
  have a1 : coeffAddr fP (st + 8 * u) + BitVec.ofNat 64 (4 * len) = coeffAddr fP (st + 8 * u + len) :=
    coeffAddr_add _ _ _
  have r0 : InRegions (s.rd ++ s.wr) (coeffAddr fP (st + 8 * u) + BitVec.ofNat 64 0) 32 := by
    rw [add_ofNat_zero]; exact f_in32 (List.mem_append_right _ hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (coeffAddr fP (st + 8 * u) + BitVec.ofNat 64 (4 * len)) 32 := by
    rw [a1]; exact f_in32 (List.mem_append_right _ hw) j1
  rw [ybody, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [hdx]; exact r0)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, hdx]; exact r1)) fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  have o12 := o1.trans o2
  generalize hP : blk G len k st (8 * u) = P at hS
  refine WP.mono (ybf_ok hbf hY (yonly_yconsts o12 hc (by decide) (by decide))
    (x := fun l e => P[st + 8 * u + 4 * l + e]!) (y := fun l e => P[st + 8 * u + len + 4 * l + e]!)
    (ζ := fun _ _ => zetas k)
    (fun l hl => by
      rw [o2.lane _ (by decide) l hl, L1 l hl, hdx, add_ofNat_zero]; exact dlanes_loadY hS j0 hl)
    (fun l hl => by
      rw [L2 l hl, o1.gpr, o1.mem, hdx, a1]; exact dlanes_loadY hS j1 hl)
    (fun l hl => by rw [o12.lane _ (by decide) l hl]; exact hz l hl)
    (fun l hl => by rw [o12.lane _ (by decide) l hl, o12.lane _ (by decide) l hl]; exact ho l hl))
    fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o12.trans o3
  have w0 : InRegions s3.wr (s3.gpr .rdx) 32 := by
    rw [o13.wr, o13.gpr, hdx]; exact f_in32 hw j0
  have w1 : InRegions s3.wr (s3.gpr .rdx + BitVec.ofNat 64 (4 * len)) 32 := by
    rw [o13.wr, o13.gpr, hdx, a1]; exact f_in32 hw j1
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1, sx32]
  have g3 : s3.gpr .rdx = coeffAddr fP (st + 8 * u) := by rw [o13.gpr, hdx]
  rw [g3, a1, o13.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have hR : ∀ i < 256, (blk G len k st (8 * (u + 1)))[i]! = if st + 8 * u ≤ i ∧ i < st + 8 * u + 8 then
        (op P[i]! P[i + len]! (zetas k)).1 else if st + 8 * u + len ≤ i ∧ i < st + 8 * u + len + 8 then
        (op P[i - len]! P[i]! (zetas k)).2 else P[i]! := fun i hi => by
      rw [← hP, show 8 * (u + 1) = 8 * u + 8 by omega, hblk.add, hblk.get _ _ _ _ _ (by omega) (by omega)
        (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    refine polyIs_write2L (s := s3) hS j0 j1 (by omega) (fun l hl e he => ?_) (fun l hl e he => ?_)
      (fun i hi h1 h2 => by rw [hR i hi, ite_eq_right (by omega), ite_eq_right (by omega)])
    · rw [(B3 l hl).1 e he]; dsimp only; rw [hR _ (by omega), ite_eq_left (by omega),
        show st + 8 * u + len + 4 * l + e = st + 8 * u + 4 * l + e + len by omega]
    · rw [(B3 l hl).2 e he]; dsimp only; rw [hR _ (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
        show st + 8 * u + len + 4 * l + e - len = st + 8 * u + 4 * l + e by omega]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add,
      show st + 8 * u + 8 = st + 8 * (u + 1) by omega]
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact ylanes_gpr (s := s3) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o13 hc
      (by decide) (by decide)
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o13.lane _ (by decide) l hl
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o13.lane _ (by decide) l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [o13.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr]
  · rw [o13.gpr]
  · rw [o13.gpr]
  · exact o13.mxcsr

/-- The code of a block of a layer with `len ≥ 8`. -/
abbrev yblk (bf : List Instr) (len : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block (yzeta1 ++ [.alu .add .r8 (.imm dz)]))
    (.seq (rcxLoop (len / 8) ([.vmovdquLoad .l256 .xmm0 (at_ .rdx 0),
        .vmovdquLoad .l256 .xmm1 (at_ .rdx (4 * len))] ++ toY bf ++
        [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx (4 * len)) .xmm3,
          .alu .add .rdx (.imm 32)]))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (4 * len))), .alu .sub .rax (.imm 1)]))

theorem yblock_ok {fP sP : Addr} {len st kz : Nat} (h8 : 8 ≤ len) (hl8 : len % 8 = 0) (hl : len ≤ 128)
    (hs : st + 2 * len ≤ 256) (hkz : kz + 4 ≤ 256) (dz : BitVec 32) {G : Poly} {s : State} (hc : YConsts s)
    (hdx : s.gpr .rdx = coeffAddr fP st) (h8r : s.gpr .r8 = coeffAddr sP kz) (hS : PolyIs s.mem fP G)
    (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (yblk bf len dz) s fun s' => PolyIs s'.mem fP (blk G len kz st len) ∧
      s'.gpr .rdx = coeffAddr fP (st + 2 * len) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      s'.gpr .rax = s.gpr .rax - 1 ∧ s'.zf = some (s.gpr .rax - 1 == 0) ∧ BInvY fP s s' := by
  -- the zeta
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (yzeta1_ok hkz h8r (tab_in (List.mem_append_right _ hw) hkz) hT) fun s1 ⟨z1, o1⟩ => ?_
  have g1 : s1.gpr = s.gpr := o1.gpr
  refine WP.mono (addR_ok .r8 dz s1) fun s2 ⟨h82, o2, y2⟩ => ?_
  have l2 := o2.lane y2
  have c2 : YConsts s2 := ylanes_gpr (s := s1) l2 o1 hc (by decide) (by decide)
  have dx2 : s2.gpr .rdx = coeffAddr fP st := by rw [o2.keep.gpr (by decide), g1, hdx]
  have hw2 : pR fP ∈ s2.wr := by rw [o2.keep.2.2, o1.wr]; exact hwf
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  refine WP.seq (WP.mono (wp_rcxLoopY (N := len / 8) (by omega) (by omega)
    (fun u w => PolyIs w.mem fP (blk G len kz st (8 * u)) ∧ w.gpr .rdx = coeffAddr fP (st + 8 * u) ∧
      YConsts w ∧ (∀ l < 2, w.lane .xmm13 l = s2.lane .xmm13 l) ∧ (∀ l < 2, w.lane .xmm12 l = s2.lane .xmm12 l) ∧
      Keep [.rcx, .rdx] s2 w ∧ Frame [pR fP] s2.mem w.mem ∧ w.mxcsr = s2.mxcsr)
    (fun w o hy _ => ⟨by rw [hblk.zero, o.mem, m2]; exact hS, by rw [o.keep.gpr (by decide), dx2]; rfl,
      ylanes_gpr (s := s2) (o.lane hy) (YOnly.refl [] s2) c2 (by decide) (by decide),
      fun l _ => o.lane hy _ l, fun l _ => o.lane hy _ l, o.keep.mono (by simp),
      by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun u hu w ⟨hS', hdx', hc', hz', hzo', hk', hf', hx'⟩ => WP.mono (ystep hbf hY hblk h8 hs (by
        have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hl8); omega) hc'
        (fun l hl => by rw [hz' l hl, l2]; exact (z1 l hl).1)
        (fun l hl => by rw [hz' l hl, hzo' l hl, l2, l2]; exact (z1 l hl).2) hdx' hS'
        (by rw [hk'.2.2]; exact hw2))
      fun w' ⟨hS'', hdx'', hf'', hc'', hz'', hzo'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', fun l hl => by rw [hz'' l hl, hz' l hl], fun l hl => by rw [hzo'' l hl, hzo' l hl],
          (hk'.trans hk'').mono (by simp), hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩))
    fun w ⟨hS3, hdx3, hc3, _, _, hk3, hf3, hx3⟩ => ?_)
  rw [show 8 * (len / 8) = len from Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl8)] at hS3 hdx3
  have hax : w.gpr .rax = s.gpr .rax := by rw [hk3.gpr (by decide), o2.keep.gpr (by decide), g1]
  have h8w : w.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [hk3.gpr (by decide), h82, g1]
  vrund [hdx3, sx_ofNat (show 4 * len < 2 ^ 31 by omega), hax, h8w]
  refine ⟨hS3, by rw [coeffAddr_add, show st + len + len = st + 2 * len by omega], ?_⟩
  have k1 : Keep [.r8, .rcx, .rdx, .rax] s w :=
    (Keep.trans (⟨fun r _ => by rw [g1], o1.rd, o1.wr⟩ : Keep [] s s1) (o2.keep.trans hk3)).mono (by simp)
  refine ⟨⟨fun r hr => ?_, k1.2.1, k1.2.2⟩, by rw [← m2]; exact hf3,
    ylanes_gpr (s := w) (fun r l => by simp only [lane_setReg, lane_setFlags]) (YOnly.refl [] w) hc3
      (by decide) (by decide),
    by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [hx3, o2.mxcsr, o1.mxcsr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  exact k1.gpr (by simp [hr])

theorem ylay_ok {fP sP : Addr} {len k : Nat} (hlen : len ∈ [8, 16, 32, 64, 128]) (dz : BitVec 32)
    (zi : Nat → Nat) (hz0 : zi 0 = k) (hzi : ∀ c < 128 / len, zi c + 4 ≤ 256)
    (hstep : ∀ c < 128 / len, coeffAddr sP (zi c) + BitVec.signExtend 64 dz = coeffAddr sP (zi (c + 1)))
    {F : Poly} {s : State} (hc : YConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay bf len k dz) s fun s' => PolyIs s'.mem fP (layF blk F len zi (128 / len)) ∧
      BInvY fP s s' := by
  have hl : 8 ≤ len ∧ len % 8 = 0 ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
      128 / len ≤ 16 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h8, hl8, hl128, hcov, hpos, h16⟩ := hl
  have hk : k + 4 ≤ 256 := hz0 ▸ hzi 0 hpos
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧ w.gpr .r8 = coeffAddr sP k ∧
      w.gpr .rax = BitVec.ofNat 64 (128 / len) ∧ GOnly [.rdx, .r8, .rax] s w ∧ w.ymmHi = s.ymmHi)
    (by
      simp only [leaR]
      vrund [sx_ofNat (show 4 * k < 2 ^ 31 by omega), hsi, hdi, RegUpd.ymmHi_setReg]
      refine ⟨?_, by gonlyd, rfl⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega) fun w ⟨hdx, h8r, hax, o, hy⟩ => ?_)
  have hwf' : pR fP ∈ w.wr := by rw [o.keep.2.2]; exact hwf
  have hw' : pR sP ∈ w.wr := by rw [o.keep.2.2]; exact hw
  have cw : YConsts w := ylanes_gpr (s := s) (o.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_countdown (cnt := .rax) (N := 128 / len) (by omega) hpos
    (fun c u => PolyIs u.mem fP (layF blk F len zi c) ∧ u.gpr .rdx = coeffAddr fP (2 * len * c) ∧
      u.gpr .r8 = coeffAddr sP (zi c) ∧ BInvY fP w u ∧ Tab zmTab u.mem sP 256)
    (fun c hc u ⟨hS', hdx', h8', hb', hT'⟩ _ => ?_) (fun u h => h)
    ⟨by rw [o.mem]; exact hS, by rw [hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [h8r, hz0], ⟨Keep.refl _ _, Frame.refl _ _, cw, rfl⟩, by rw [o.mem]; exact hT⟩ hax)
    fun u ⟨hS', _, _, hb', _⟩ => ⟨hS', ⟨(o.keep.trans hb'.keep).mono (by simp),
      by rw [← o.mem]; exact hb'.frame, hb'.consts, by rw [hb'.mxcsr, o.mxcsr]⟩⟩
  have hs : 2 * len * c + 2 * len ≤ 256 := by
    have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (yblock_ok hbf hY hblk h8 hl8 hl128 hs (hzi c hc) dz hb'.consts hdx' h8' hS' hT'
    (by rw [hb'.keep.2.2]; exact hwf') (by rw [hb'.keep.2.2]; exact hw'))
    fun u' ⟨hS'', hdx'', h8'', hax'', hzf'', hb''⟩ =>
      ⟨⟨by rw [layF, foldl_range_succ]; exact hS'', by rw [hdx'', Nat.mul_succ],
        by rw [h8'', h8', hstep c hc], hb'.trans hb'',
        hT'.frame hb''.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)⟩, hax'', hzf''⟩

/-! ## The layer with `len = 4` -/

/-- The body of the layer with `len = 4`. -/
abbrev ybody4 (bf : List Instr) (o₀ o₁ : BitVec 8) (dz : BitVec 32) : List Instr :=
  [.vmovdquLoad .l256 .xmm4 (at_ .rdx 0)] ++ ([.vmovdquLoad .l256 .xmm5 (at_ .rdx 32)] ++ (yzetaS o₀ o₁ ++
    ([.alu .add .r8 (.imm dz)] ++ ([.vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20)] ++
    ([.vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] ++ (toY bf ++ ([.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20)] ++
    ([.vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31)] ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm4, .vmovdquStore .l256 (at_ .rdx 32) .xmm5, .alu .add .rdx (.imm 64),
      .alu .sub .rcx (.imm 1)]))))))))

theorem ystep4 {fP sP : Addr} {m kb : Nat} (hm : m < 16) (o₀ o₁ : BitVec 8) (dz : BitVec 32) (zi : Nat → Nat)
    (hk : kb + 4 ≤ 256) (hsel : ∀ e < 4, kb + sel o₀ e = zi (2 * m) ∧ kb + sel o₁ e = zi (2 * m + 1))
    {F : Poly} {s : State} (hc : YConsts s) (hdx : s.gpr .rdx = coeffAddr fP (16 * m))
    (h8 : s.gpr .r8 = coeffAddr sP kb) (hS : PolyIs s.mem fP (layF blk F 4 zi (2 * m)))
    (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (.block (ybody4 bf o₀ o₁ dz)) s fun s' =>
      PolyIs s'.mem fP (layF blk F 4 zi (2 * (m + 1))) ∧ s'.gpr .rdx = coeffAddr fP (16 * (m + 1)) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInvY fP s s' := by
  have j0 : 16 * m + 8 ≤ 256 := by omega
  have j1 : 16 * m + 8 + 8 ≤ 256 := by omega
  have a1 : coeffAddr fP (16 * m) + BitVec.ofNat 64 32 = coeffAddr fP (16 * m + 8) := coeffAddr_add _ _ 8
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact f_in32 (List.mem_append_right s.rd hwf) j0
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [hdx, a1]; exact f_in32 (List.mem_append_right s.rd hwf) j1
  generalize hP : layF blk F 4 zi (2 * m) = P at hS
  -- the loads
  rw [ybody4, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L4, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L5, o2⟩ => ?_
  have o12 := o1.trans o2
  -- the zetas
  rw [WP.block_append_iff]
  have hk0 : ∀ j < 4, kb + sel o₀ j < 256 := fun j _ => by have := sel_lt o₀ j; omega
  have hk1 : ∀ j < 4, kb + sel o₁ j < 256 := fun j _ => by have := sel_lt o₁ j; omega
  refine WP.mono (yzetaS_ok o₀ o₁ (zP := sP) (k := kb) hk0 hk1 (by rw [o12.gpr, h8])
    (by rw [o12.rd, o12.wr]; exact tab_in (List.mem_append_right _ hw) hk) (by rw [o12.mem]; exact hT))
    fun s3 ⟨Z0, Z1, ZO, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addR_ok .r8 dz s3) fun s4 ⟨h84, g4, y4⟩ => ?_
  have l4 := g4.lane y4
  -- the lower and upper halves
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s4) fun s5 ⟨P5, o5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s5) fun s6 ⟨P6, o6⟩ => ?_
  have c6 : YConsts s6 := yonly_yconsts (o5.trans o6)
    (ylanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide)) (by decide) (by decide)
  have m3 : s3.mem = s.mem := (o12.trans o3).mem
  have q4 : ∀ l < 2, s4.lane .xmm4 l = s.mem.readW (coeffAddr fP (16 * m) + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by rw [l4, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl, L4 l hl, hdx, add_ofNat_zero]
  have q5 : ∀ l < 2, s4.lane .xmm5 l =
      s.mem.readW (coeffAddr fP (16 * m + 8) + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by rw [l4, o3.lane _ (by decide) l hl, L5 l hl, o1.gpr, o1.mem, hdx, a1]
  rw [WP.block_append_iff]
  refine WP.mono (ybf_ok hbf hY c6 (x := fun l e => P[16 * m + 8 * l + e]!)
    (y := fun l e => P[16 * m + 8 * l + 4 + e]!) (ζ := fun l _ => zetas (zi (2 * m + l)))
    (fun l hl => by
      rw [o6.lane _ (by decide) l hl, P5 l hl, perm20 _ _ hl]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, q4 0 (by decide)]
        exact (dlanes_loadY hS j0 (by decide)).congr fun e _ => getP_congr P (by omega)
      · rw [ifn (by decide), q5 0 (by decide)]
        exact (dlanes_loadY hS j1 (by decide)).congr fun e _ => getP_congr P (by omega))
    (fun l hl => by
      rw [P6 l hl, perm31 _ _ hl, o5.lane .xmm4 (by decide) 1 (by decide), o5.lane .xmm5 (by decide) 1 (by decide)]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, q4 1 (by decide)]
        exact (dlanes_loadY hS j0 (by decide)).congr fun e _ => getP_congr P (by omega)
      · rw [ifn (by decide), q5 1 (by decide)]
        exact (dlanes_loadY hS j1 (by decide)).congr fun e _ => getP_congr P (by omega))
    (fun l hl => by
      rw [(o5.trans o6).lane _ (by decide) l hl, l4]
      rcases lane01 hl with rfl | rfl
      · exact Z0.congr fun i hi => congrArg zetas (hsel i hi).1
      · exact Z1.congr fun i hi => congrArg zetas (hsel i hi).2)
    (fun l hl => by
      rw [(o5.trans o6).lane _ (by decide) l hl, (o5.trans o6).lane _ (by decide) l hl, l4, l4]
      exact ZO l hl))
    fun s7 ⟨B7, o7⟩ => ?_
  -- the blocks back
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s7) fun s8 ⟨P8, o8⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yperm_ok s8) fun s9 ⟨P9, o9⟩ => ?_
  have o59 := (o5.trans o6).trans (o7.trans (o8.trans o9))
  have w0 : InRegions s9.wr (s9.gpr .rdx) 32 := by
    rw [o59.wr, o59.gpr, g4.keep.2.2, g4.keep.gpr (by decide), o3.wr, o3.gpr, o12.wr, o12.gpr, hdx]
    exact f_in32 hwf j0
  have w1 : InRegions s9.wr (s9.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [o59.wr, o59.gpr, g4.keep.2.2, g4.keep.gpr (by decide), o3.wr, o3.gpr, o12.wr, o12.gpr, hdx, a1]
    exact f_in32 hwf j1
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  have g9 : s9.gpr = s4.gpr := o59.gpr
  have m9 : s9.mem = s.mem := by rw [o59.mem, g4.mem, m3]
  have dx9 : s9.gpr .rdx = coeffAddr fP (16 * m) := by
    rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr, hdx]
  rw [dx9, a1, m9]
  have hR : ∀ i < 256, (layF blk F 4 zi (2 * (m + 1)))[i]! = if 16 * m ≤ i ∧ i < 16 * m + 16 then
      (if i % (2 * 4) < 4 then (op P[i]! P[i + 4]! (zetas (zi (i / (2 * 4))))).1
        else (op P[i - 4]! P[i]! (zetas (zi (i / (2 * 4))))).2) else P[i]! := fun i hi => by
    have hF : ∀ j, 16 * m ≤ j → j < 256 → P[j]! = F[j]! := fun j h1 h2 => by
      rw [← hP, layF_get hblk F (by decide) zi (by omega) h2, ite_eq_right (by omega)]
    rw [layF_get hblk F (by decide) zi (by omega) hi]
    by_cases h1 : 16 * m ≤ i ∧ i < 16 * m + 16
    · rw [ite_eq_left (by omega), ite_eq_left h1]
      by_cases h2 : i % (2 * 4) < 4
      · rw [ite_eq_left h2, ite_eq_left h2, hF _ h1.1 hi, hF _ (by omega) (by omega)]
      · rw [ite_eq_right h2, ite_eq_right h2, hF _ (by omega) (by omega), hF _ h1.1 hi]
    · rw [ite_eq_right h1, ← hP, layF_get hblk F (by decide) zi (by omega) hi]
      by_cases h3 : i < 16 * m
      · rw [ite_eq_left (show i < 2 * 4 * (2 * (m + 1)) by omega),
          ite_eq_left (show i < 2 * 4 * (2 * m) by omega)]
      · rw [ite_eq_right (show ¬ i < 2 * 4 * (2 * (m + 1)) by omega),
          ite_eq_right (show ¬ i < 2 * 4 * (2 * m) by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · refine polyIs_write2L (s := s9) hS j0 j1 (by omega) (fun l hl => ?_) (fun l hl => ?_)
      (fun i hi h1 h2 => by rw [hR i hi, ite_eq_right (by omega)])
    · rw [o9.lane .xmm4 (by decide) l hl, P8 l hl, perm20 _ _ hl]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl]
        exact (B7 0 (by decide)).1.congr fun e he => by
          rw [hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
          exact congrArg Prod.fst (op_idx op P zi (by omega) (by omega) (by omega))
      · rw [ifn (by decide)]
        exact (B7 0 (by decide)).2.congr fun e he => by
          rw [hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
          exact congrArg Prod.snd (op_idx op P zi (by omega) (by omega) (by omega))
    · rw [P9 l hl, perm31 _ _ hl, o8.lane .xmm0 (by decide) 1 (by decide),
        o8.lane .xmm3 (by decide) 1 (by decide)]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl]
        exact (B7 1 (by decide)).1.congr fun e he => by
          rw [hR _ (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
          exact congrArg Prod.fst (op_idx op P zi (by omega) (by omega) (by omega))
      · rw [ifn (by decide)]
        exact (B7 1 (by decide)).2.congr fun e he => by
          rw [hR _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
          exact congrArg Prod.snd (op_idx op P zi (by omega) (by omega) (by omega))
  · rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) by decide, coeffAddr_add,
      Nat.mul_succ]
  · rw [g9, h84, o3.gpr, o12.gpr]
  · rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, State.setMem_gpr]
    rw [g9, g4.keep.gpr (by simp [hr]), o3.gpr, o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]
    rw [o59.rd, g4.keep.2.1, o3.rd, o12.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]
    rw [o59.wr, g4.keep.2.2, o3.wr, o12.wr]
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact ylanes_gpr (s := s9) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane])
      o59 (ylanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide)) (by decide) (by decide)
  · exact o59.mxcsr.trans (g4.mxcsr.trans (o12.trans o3).mxcsr)

theorem ylay4_ok {fP sP : Addr} (k : Nat) (o₀ o₁ : BitVec 8) (dz : BitVec 32) (zi kb : Nat → Nat)
    (hkb0 : kb 0 = k) (hk : ∀ m < 16, kb m + 4 ≤ 256)
    (hsel : ∀ m < 16, ∀ e < 4, kb m + sel o₀ e = zi (2 * m) ∧ kb m + sel o₁ e = zi (2 * m + 1))
    (hstep : ∀ m < 16, coeffAddr sP (kb m) + BitVec.signExtend 64 dz = coeffAddr sP (kb (m + 1)))
    {F : Poly} {s : State} (hc : YConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay4 bf k o₀ o₁ dz) s fun s' => PolyIs s'.mem fP (layF blk F 4 zi 32) ∧ BInvY fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega
  refine WP.seq (WP.mono (ypre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 4 zi (2 * i)) ∧ u.gpr .rdx = coeffAddr fP (16 * i) ∧
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
  rw [show [Instr.vmovdquLoad .l256 .xmm4 (at_ .rdx 0), .vmovdquLoad .l256 .xmm5 (at_ .rdx 32)] ++ yzetaS o₀ o₁ ++
      [.alu .add .r8 (.imm dz), .vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20),
        .vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] ++ toY bf ++
      [.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20), .vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31),
        .vmovdquStore .l256 (at_ .rdx 0) .xmm4, .vmovdquStore .l256 (at_ .rdx 32) .xmm5,
        .alu .add .rdx (.imm 64)] ++ [.alu .sub .rcx (.imm 1)] = ybody4 bf o₀ o₁ dz by
    simp [List.append_assoc]]
  exact WP.mono (ystep4 hbf hY hblk hi o₀ o₁ dz zi (hk i hi) (hsel i hi) hb'.consts hdx' h8' hS' hT' hwf' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', by rw [h8'', h8', hstep i hi],
      hb'.trans hb''⟩, hcx, hzf⟩

end

end VG.Proof.MlDsa.X86_64.Arith
