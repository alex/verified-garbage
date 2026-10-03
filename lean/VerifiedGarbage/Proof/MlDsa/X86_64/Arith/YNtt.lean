import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv

/-!
# ML-DSA on x86-64: `vg_mldsa_ntt_avx2` and `vg_mldsa_inv_ntt_avx2`

As `vg_mldsa_ntt` and `vg_mldsa_inv_ntt` (`Ntt.lean`, `NttInv.lean`): ML-KEM's
`withMxcsr` runs the code from any MXCSR and keeps what it does
(`ymx_correct`); the prologue leaves the table of zetas in `scratch` and the
constants in both lanes (`ypro_ok`); each layer is `nttLayer` or `nttInvLayer`
(`ylay_ok`, `ylay4_ok`, `ylay2_ok`, `ylay1_ok`), `NTT⁻¹` then multiplies every
coefficient by `8347681 = 256⁻¹ mod q` (`yscale_ok`), and `vzeroupper` keeps
the memory (`LIY.epi`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok ifp ifn sel GOnly WP.keep writesOnly
  gprPreserved_of withMxcsr_ok mxR add_ofNat_zero wp_rcxLoopY lane_setReg lane_setFlags State.setMem_ymm sx32)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop yconst)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt PolyIs zetas ntt nttInv)

theorem lane_vbfly : laneSseBlock (toY vbfly) = some vbfly := by decide +kernel
theorem lane_vibfly : laneSseBlock (toY vibfly) = some vibfly := by decide +kernel
theorem lane_core2f : laneSseBlock (toY (gath2 ++ vbfly ++ scat2)) = some (gath2 ++ vbfly ++ scat2) := by
  decide +kernel
theorem lane_core2i : laneSseBlock (toY (gath2 ++ vibfly ++ scat2)) = some (gath2 ++ vibfly ++ scat2) := by
  decide +kernel
theorem lane_core1f : laneSseBlock (toY (gath1 ++ vbfly ++ scat1)) = some (gath1 ++ vbfly ++ scat1) := by
  decide +kernel
theorem lane_core1i : laneSseBlock (toY (gath1 ++ vibfly ++ scat1)) = some (gath1 ++ vibfly ++ scat1) := by
  decide +kernel
theorem lane_vmul3 : laneSseBlock (toY (vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++ vcsub .xmm3 .xmm2)) =
    some (vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++ vcsub .xmm3 .xmm2) := by decide +kernel

/-! ## The prologue and the layers -/

/-- The table of zetas and the constants. -/
theorem ypro_ok {sP : Addr} {s : State} (hsi : s.gpr .rsi = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block ypro) s fun s' => Tab zmTab s'.mem sP 256 ∧ YConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9, .rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [ypro, WP.block_append_iff]
  refine WP.mono (dwordTab_ok zmTab (fun k => Nat.lt_trans (zmTab_lt k) (by decide)) (by decide) hsi hw)
    fun s1 ⟨hT, hf, k1, x1, _⟩ => WP.mono (yconsts_ok s1) fun s2 ⟨hc, k2, m2, x2, _⟩ =>
      ⟨by rw [m2]; exact hT, hc, by rw [m2]; exact hf, (k1.trans k2).mono (by simp), by rw [x2, x1]⟩

/-- Between the layers: the polynomial `F` at `fP`, the table at `sP`, and
the constants in both lanes. -/
structure LIY (fP sP : Addr) (s₀ : State) (F : Poly) (s : State) : Prop where
  P : PolyIs s.mem fP F
  T : Tab zmTab s.mem sP 256
  c : YConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem

/-- A layer, then `c`. -/
theorem LIY.seq {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l c : Prog isa}
    {F F' : Poly} {Q : State → Prop}
    (hl : ∀ s, YConsts s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F → Tab zmTab s.mem sP 256 →
      pR fP ∈ s.wr → pR sP ∈ s.wr → WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInvY fP s s')
    (hc : ∀ s, LIY fP sP s₀ F' s → WP isa c s Q) {s : State} (hI : LIY fP sP s₀ F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

/-- `vzeroupper` keeps the memory. -/
theorem LIY.epi {fP sP : Addr} {s₀ : State} {F : Poly} {s : State} (hI : LIY fP sP s₀ F s) :
    WP isa (.block yepi) s fun s' => PolyIs s'.mem fP F ∧ Frame [pR fP] s₀.mem s'.mem :=
  WP.mono (Q := fun (u : State) => u.mem = s.mem) (by simp only [yepi]; vrund; rfl)
    fun u hm => by rw [hm]; exact ⟨hI.P, hI.frame⟩

/-- A layer of `NTT` with `len ≥ 8`, whose first zeta is `zetas k`. -/
theorem yfwdLay_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) (len k : Nat)
    (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 128 / len = k) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay vbfly len k 4) s fun s' => PolyIs s'.mem fP (nttLayer F len) ∧ BInvY fP s s' := by
  rw [nttLayer_eq]
  exact ylay_ok vbfly_spec lane_vbfly nttBlk_ok hlen 4 (fun c => 128 / len + c) (by rw [hk]; rfl)
    (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      rcases hlen with rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun c _ => step_fwd _ _ 1 (by decide)) hc hdi hsi hS hT hwf hw hd

theorem yfwdLay4_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 vbfly 32 0x00 0x55 8) s fun s' => PolyIs s'.mem fP (nttLayer F 4) ∧ BInvY fP s s' := by
  have h0 : ∀ e < 4, sel 0x00 e = 0 := by decide
  have h5 : ∀ e < 4, sel 0x55 e = 1 := by decide
  rw [nttLayer_eq, show 128 / 4 = 32 from rfl]
  exact ylay4_ok vbfly_spec lane_vbfly nttBlk_ok 32 0x00 0x55 8 (fun c => 32 + c) (fun m => 32 + 2 * m) rfl
    (fun m _ => by omega) (fun m _ e he => ⟨by rw [h0 e he]; omega, by rw [h5 e he]; omega⟩)
    (fun m _ => (step_fwd _ _ 2 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd

theorem yfwdLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 vbfly 64 0xA0 0xF5 16) s fun s' => PolyIs s'.mem fP (nttLayer F 2) ∧ BInvY fP s s' := by
  have hA : ∀ e < 4, sel 0xA0 e = 2 * (e / 2) := by decide
  have hF : ∀ e < 4, sel 0xF5 e = 1 + 2 * (e / 2) := by decide
  rw [nttLayer_eq, show 128 / 2 = 64 from rfl]
  exact ylay2_ok nttBlk_ok vbfly_spec lane_core2f 64 0xA0 0xF5 16 (fun c => 64 + c) (fun i => 64 + 4 * i) rfl
    (fun i _ => by omega) (fun i _ e he => ⟨by rw [hA e he]; omega, by rw [hF e he]; omega⟩)
    (fun i _ => (step_fwd _ _ 4 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd

theorem yfwdLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay1 vbfly 128 yzeta8 32) s fun s' => PolyIs s'.mem fP (nttLayer F 1) ∧ BInvY fP s s' := by
  rw [nttLayer_eq, show 128 / 1 = 128 from rfl]
  exact ylay1_ok nttBlk_ok vbfly_spec lane_core1f 128 yzeta8 32 (fun c => 128 + c) (fun i => 128 + 8 * i) rfl
    (fun i _ => by omega)
    (fun i hi s h8 hin hT => WP.mono (yzeta8_ok (by omega) h8 hin hT) fun _ ⟨z, o⟩ =>
      ⟨fun l hl => ⟨(z l hl).1.congr fun e he => congrArg zetas (by omega), (z l hl).2⟩, o⟩)
    (fun i _ => (step_fwd _ _ 8 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd

theorem yinvLay_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) (len k : Nat)
    (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 256 / len - 1 = k) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay vibfly len k (-4)) s fun s' => PolyIs s'.mem fP (nttInvLayer F len) ∧ BInvY fP s s' := by
  have hl : 128 / len ≥ 1 ∧ 256 / len = 2 * (128 / len) ∧ 256 / len ≤ 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [nttInvLayer_eq]
  exact ylay_ok vibfly_spec lane_vibfly nttInvBlk_ok hlen (-4) (fun c => 256 / len - 1 - c) (by rw [hk]; rfl)
    (fun c _ => by omega)
    (fun c hc' => (congrArg (· + _) (congrArg (coeffAddr sP) (show 256 / len - 1 - c =
      256 / len - 1 - (c + 1) + 1 by omega))).trans (step_bwd _ _ 1 (by decide)))
    hc hdi hsi hS hT hwf hw hd

theorem yinvLay4_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 vibfly 62 0x55 0x00 (-8)) s fun s' => PolyIs s'.mem fP (nttInvLayer F 4) ∧ BInvY fP s s' := by
  have h0 : ∀ e < 4, sel 0x00 e = 0 := by decide
  have h5 : ∀ e < 4, sel 0x55 e = 1 := by decide
  rw [nttInvLayer_eq, show 256 / 4 - 1 = 63 from rfl, show 128 / 4 = 32 from rfl]
  exact ylay4_ok vibfly_spec lane_vibfly nttInvBlk_ok 62 0x55 0x00 (-8) (fun c => 63 - c) (fun m => 62 - 2 * m)
    rfl (fun m _ => by omega) (fun m _ e he => ⟨by rw [h5 e he]; omega, by rw [h0 e he]; omega⟩)
    (fun m _ => (congrArg (· + _) (congrArg (coeffAddr sP) (show 62 - 2 * m = 62 - 2 * (m + 1) + 2 by
      omega))).trans (step_bwd _ _ 2 (by decide))) hc hdi hsi hS hT hwf hw hd

theorem yinvLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 vibfly 124 0x5F 0x0A (-16)) s fun s' => PolyIs s'.mem fP (nttInvLayer F 2) ∧
      BInvY fP s s' := by
  have hA : ∀ e < 4, sel 0x5F e = 3 - 2 * (e / 2) := by decide
  have hB : ∀ e < 4, sel 0x0A e = 2 - 2 * (e / 2) := by decide
  rw [nttInvLayer_eq, show 256 / 2 - 1 = 127 from rfl, show 128 / 2 = 64 from rfl]
  exact ylay2_ok nttInvBlk_ok vibfly_spec lane_core2i 124 0x5F 0x0A (-16) (fun c => 127 - c)
    (fun i => 124 - 4 * i) rfl (fun i _ => by omega)
    (fun i _ e he => ⟨by rw [hA e he]; omega, by rw [hB e he]; omega⟩)
    (fun i _ => (congrArg (· + _) (congrArg (coeffAddr sP) (show 124 - 4 * i = 124 - 4 * (i + 1) + 4 by
      omega))).trans (step_bwd _ _ 4 (by decide))) hc hdi hsi hS hT hwf hw hd

theorem yinvLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay1 vibfly 248 yzeta8R (-32)) s fun s' => PolyIs s'.mem fP (nttInvLayer F 1) ∧
      BInvY fP s s' := by
  rw [nttInvLayer_eq, show 256 / 1 - 1 = 255 from rfl, show 128 / 1 = 128 from rfl]
  exact ylay1_ok nttInvBlk_ok vibfly_spec lane_core1i 248 yzeta8R (-32) (fun c => 255 - c)
    (fun i => 248 - 8 * i) rfl (fun i _ => by omega)
    (fun i hi s h8 hin hT => WP.mono (yzeta8R_ok (by omega) h8 hin hT) fun _ ⟨z, o⟩ =>
      ⟨fun l hl => ⟨(z l hl).1.congr fun e he => congrArg zetas (by omega), (z l hl).2⟩, o⟩)
    (fun i _ => (congrArg (· + _) (congrArg (coeffAddr sP) (show 248 - 8 * i = 248 - 8 * (i + 1) + 8 by
      omega))).trans (step_bwd _ _ 8 (by decide))) hc hdi hsi hS hT hwf hw hd

/-! ## The multiplication by `256⁻¹` -/

/-- The coefficients of `G` before `8i` multiplied by `8347681`. -/
def YScaled (m : Mem) (fP : Addr) (G : Poly) (i : Nat) : Prop :=
  ∀ k < 256, (coeffAt m fP k).toNat = (if k < 8 * i then G[k]! * 8347681 else G[k]!).val

/-- `8347681 · 2³² mod q` in each doubleword. -/
theorem scale_lanes : ZLanes (ofDwords 16382#32 16382#32 16382#32 16382#32) (fun _ => 8347681) ∧
    ZOdd (ofDwords 16382#32 16382#32 16382#32 16382#32) (ofDwords 16382#32 16382#32 16382#32 16382#32) :=
  ⟨fun i hi => by rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide,
    fun j hj => by rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide⟩

theorem mov12_ok (t : State) :
    WP isa (.block [xmov .xmm12 .xmm13]) t fun t' => t'.xmm .xmm12 = t.xmm .xmm13 ∧ XOnly [.xmm12] t t' := by
  simp only [xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

/-- The body of the loop of `yscale`. -/
abbrev sbodyY : List Instr :=
  [.vmovdquLoad .l256 .xmm3 (at_ .rdx 0)] ++ toY (vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++ vcsub .xmm3 .xmm2) ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 32)] ++ [.alu .sub .rcx (.imm 1)]

theorem yscale_step {fP : Addr} {G : Poly} {i : Nat} (hi : i < 32) {s : State} (hc : YConsts s)
    (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun _ => 8347681))
    (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l))
    (hdx : s.gpr .rdx = coeffAddr fP (8 * i)) (hS : YScaled s.mem fP G i) (hw : pR fP ∈ s.wr) :
    WP isa (.block sbodyY) s fun s' =>
      YScaled s'.mem fP G (i + 1) ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
        Frame [pR fP] s.mem s'.mem ∧ YConsts s' ∧ (∀ l < 2, s'.lane .xmm13 l = s.lane .xmm13 l) ∧
        (∀ l < 2, s'.lane .xmm12 l = s.lane .xmm12 l) ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact f_in32 (List.mem_append_right _ hw) j0
  rw [sbodyY, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_vmul3 (P := fun l t =>
      t.xmm .xmm3 = csubV (montV (s1.lane .xmm3 l) (s1.lane .xmm13 l) (s1.lane .xmm12 l)))
    fun l hl => vmul3_ok (yonly_yconsts o1 hc (by decide) (by decide) l hl)) fun s2 ⟨V2, o2⟩ => ?_
  have o12 := o1.trans o2
  have hv : ∀ l < 2, ∀ e < 4, (dword (s2.lane .xmm3 l) e).toNat = (G[8 * i + 4 * l + e]! * 8347681).val := by
    intro l hl e he
    have hx : DLanes (s1.lane .xmm3 l) (fun e => G[8 * i + 4 * l + e]!) := fun e he => by
      rw [L1 l hl, hdx, add_ofNat_zero, dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq,
        hS _ (by omega), ifn (by omega)]
    have hz' : ZLanes (s1.lane .xmm13 l) (fun _ => 8347681) := by
      rw [o1.lane _ (by decide) l hl]; exact hz l hl
    have ho' : ZOdd (s1.lane .xmm13 l) (s1.lane .xmm12 l) := by
      rw [o1.lane _ (by decide) l hl, o1.lane _ (by decide) l hl]; exact ho l hl
    have e2 : s2.lane .xmm3 l = _ := V2 l hl
    rw [e2, dword_csubV _ he, mulZ (hx e he) (hz' e he) (dword_montV ho' (prod_lt hx hz') he)]
    dsimp only
    rw [Fin.mul_comm]
  have w0 : InRegions s2.wr (s2.gpr .rdx) 32 := by rw [o12.wr, o12.gpr, hdx]; exact f_in32 hw j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    w0, sx32]
  have g2 : s2.gpr .rdx = coeffAddr fP (8 * i) := by rw [o12.gpr, hdx]
  rw [g2, o12.mem]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
      split
      · have := hv 0 (by decide) (k - 8 * i) (by omega)
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega] at this; exact this
      · have := hv 1 (by decide) (k - 8 * i - 4) (by omega)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega] at this; exact this
    · rename_i h
      rw [hS k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add,
      show 8 * i + 8 = 8 * (i + 1) by omega]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pR_contains32 fP j0)
  · exact ylanes_gpr (s := s2) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o12 hc
      (by decide) (by decide)
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o12.lane _ (by decide) l hl
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o12.lane _ (by decide) l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o12.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o12.wr]
  · rw [o12.gpr]
  · rw [o12.gpr]
  · exact o12.mxcsr

/-- Every coefficient times `8347681`. -/
theorem yscale_ok {fP sP : Addr} (_hd : (pR sP).Disjoint (pR fP)) {G : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (_hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP G) (_hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (_hw : pR sP ∈ s.wr) :
    WP isa yscale s fun s' => PolyIs s'.mem fP (G.map (· * 8347681)) ∧ BInvY fP s s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧ GOnly [.rdx] s w ∧ w.ymmHi = s.ymmHi)
    (by vrund [hdi]; exact ⟨by gonlyd, rfl⟩) fun w ⟨hdx, og, hy⟩ => ?_
  refine WP.mono (yconst_ok .xmm13 16382 w) fun w1 ⟨l1, k1, m1, x1, o1⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm12 = w1.lane .xmm13 l)
    fun l _ => mov12_ok (w1.proj l)) fun w2 ⟨l2, o2⟩ => ?_
  have cw : YConsts w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  have cw2 : YConsts w2 := yonly_yconsts o2 (fun l hl =>
    ⟨by rw [State.proj_xmm, o1 _ (by decide) l hl]; exact (cw l hl).q,
      by rw [State.proj_xmm, o1 _ (by decide) l hl]; exact (cw l hl).qinv⟩) (by decide) (by decide)
  have z13 : ∀ l < 2, w2.lane .xmm13 l = ofDwords 16382#32 16382#32 16382#32 16382#32 := fun l hl => by
    rw [o2.lane _ (by decide) l hl, l1 l hl]; rfl
  have z12 : ∀ l < 2, w2.lane .xmm12 l = ofDwords 16382#32 16382#32 16382#32 16382#32 := fun l hl => by
    have e : w2.lane .xmm12 l = _ := l2 l hl
    rw [e, l1 l hl]; rfl
  have dx2 : w2.gpr .rdx = fP := by rw [o2.gpr, k1.gpr (by decide), hdx]
  have mw2 : w2.mem = s.mem := by rw [o2.mem, m1, og.mem]
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide)
    (fun i u => YScaled u.mem fP G i ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧ YConsts u ∧
      (∀ l < 2, u.lane .xmm13 l = w2.lane .xmm13 l) ∧ (∀ l < 2, u.lane .xmm12 l = w2.lane .xmm12 l) ∧
      Keep [.rcx, .rdx] w2 u ∧ Frame [pR fP] w2.mem u.mem ∧ u.mxcsr = w2.mxcsr)
    (fun u o hu _ => ⟨fun k hk => by
        rw [o.mem, mw2, ifn (by omega)]; exact polyIs_toNat hS (by rw [n_eq]; exact hk),
      by rw [o.keep.gpr (by decide), dx2, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      ylanes_gpr (s := w2) (o.lane hu) (YOnly.refl [] w2) cw2 (by decide) (by decide),
      fun l _ => o.lane hu _ l, fun l _ => o.lane hu _ l, o.keep.mono (by simp),
      by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun i hi u ⟨hS', hdx', hc', hz', hzo', hk', hf', hx'⟩ => WP.mono (yscale_step hi hc'
        (fun l hl => by rw [hz' l hl, z13 l hl]; exact scale_lanes.1)
        (fun l hl => by rw [hz' l hl, hzo' l hl, z13 l hl, z12 l hl]; exact scale_lanes.2) hdx' hS'
        (by rw [hk'.2.2, o2.wr, k1.2.2, og.keep.2.2]; exact hwf))
      fun u' ⟨hS'', hdx'', hf'', hc'', hz'', hzo'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', fun l hl => by rw [hz'' l hl, hz' l hl], fun l hl => by rw [hzo'' l hl, hzo' l hl],
          (hk'.trans hk'').mono (by simp), hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩))
    fun u ⟨hS', _, hc', _, _, hk', hf', hx'⟩ => ?_
  have kw2 : Keep [.rdx, .rax] s w2 :=
    ((og.keep.trans k1).trans (⟨fun r _ => by rw [o2.gpr], o2.rd, o2.wr⟩ : Keep [] w1 w2)).mono (by simp)
  refine ⟨polyIs_of_toNat fun k hk => ?_, ⟨(kw2.trans hk').mono (by simp), by rw [← mw2]; exact hf', hc',
    by rw [hx', o2.mxcsr, x1, og.mxcsr]⟩⟩
  rw [n_eq] at hk
  rw [hS' k hk, ifp (by omega), map_mul_get _ _ (by rw [n_eq]; exact hk)]

/-! ## The functions -/

/-- The code in `withMxcsr`, from its state `s1`: the prologue, then the
layers `l`, which leave `G`. -/
theorem ynttBody_ok {t : Poly → Poly} {s s1 : State} (hs : (inPlaceK t).pre s) {l : Prog isa} {G : Poly}
    (k1 : Keep [.rax, .r11] s s1) (f1 : Frame [mxR (s.gpr .rsi)] s.mem s1.mem)
    (hl : ∀ s2, LIY (s.gpr .rdi) (s.gpr .rsi) s2 (polyAt s.mem (s.gpr .rdi)) s2 → s2.gpr .rdi = s.gpr .rdi →
      s2.gpr .rsi = s.gpr .rsi → pR (s.gpr .rdi) ∈ s2.wr → pR (s.gpr .rsi) ∈ s2.wr →
      WP isa l s2 fun s3 => PolyIs s3.mem (s.gpr .rdi) G ∧ Frame [pR (s.gpr .rdi)] s2.mem s3.mem) :
    WP isa (.seq (.block ypro) l) s1 fun s' =>
      PolyIs s'.mem (s.gpr .rdi) G ∧ Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
  have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
  have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _))
      ⟨hs.2.2.2.2.2, rfl⟩
  refine WP.seq (WP.mono (ypro_ok hsi1 (by rw [k1.2.2]; exact hw)) fun s2 ⟨hT, hc, hf2, k2, _⟩ => ?_)
  have hF2 : PolyIs s2.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hF1
  refine WP.mono (hl s2 ⟨hF2, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    (by rw [k2.gpr (by decide), hdi1]) (by rw [k2.gpr (by decide), hsi1])
    (by rw [k2.2.2, k1.2.2]; exact hwf) (by rw [k2.2.2, k1.2.2]; exact hw)) fun s3 ⟨hP, hf3⟩ => ⟨hP, ?_⟩
  refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans (frame_fs hf3 ?_)) <;>
    intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
  exacts [.inr (mx_sub' _), .inr fun _ h => h, .inl fun _ h => h]

/-- `withMxcsr` around the body, and the ABI. -/
theorem ymx_correct {t : Poly → Poly} {l : Prog isa} (s : State) (hs : (inPlaceK t).pre s)
    (hk : writesOnly [.rax, .rcx, .rdx, .r8, .r9] (.seq (.block ypro) l) = true)
    (hctl : ctlOk (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block ypro) l)) = true)
    (hk' : writesOnly [.rax, .rcx, .rdx, .r8, .r9, .r11]
      (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block ypro) l)) = true)
    (hl : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxR (s.gpr .rsi)] s.mem s1.mem →
      WP isa (.seq (.block ypro) l) s1 fun s' => PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem) :
    ∃ tr s', Exec isa (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block ypro) l)) s tr s' ∧
      abiPreserved s s' ∧ (inPlaceK t).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW := withMxcsr_ok (c := .seq (.block ypro) l) (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw
    hk (hl)
  obtain ⟨tr, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW hk'
  refine ⟨tr, s', he, abiPreserved_of_ctl hctl he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub' _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _)) hP

theorem nttY_correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa nttAvx2 s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine ymx_correct s hs (by decide +kernel) (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    WP.mono (ynttBody_ok hs k1 f1 (G := nttLens.foldl nttLayer (polyAt s.mem (s.gpr .rdi)))
      fun s2 hI hdi hsi hwf hw => ?_) fun s' ⟨hP, hf⟩ => ⟨by rw [ntt_eq_layers]; exact hP, hf⟩
  simp only [nttLens, List.foldl_cons, List.foldl_nil]
  refine LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 128 1 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 64 2 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 32 4 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 16 8 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 8 16 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay4_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay2_ok hd) ?_ hI
  exact fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay1_ok hd) (fun _ hI => hI.epi) hI

theorem nttInvY_correct (s : State) (hs : (inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa nttInvAvx2 s t s' ∧ abiPreserved s s' ∧ (inPlaceK nttInv).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine ymx_correct s hs (by decide +kernel) (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    WP.mono (ynttBody_ok hs k1 f1
      (G := (nttInvLens.foldl nttInvLayer (polyAt s.mem (s.gpr .rdi))).map (· * 8347681))
      fun s2 hI hdi hsi hwf hw => ?_) fun s' ⟨hP, hf⟩ => ⟨by rw [nttInv_eq_layers]; exact hP, hf⟩
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
  refine LIY.seq hdi hsi hwf hw hd (yinvLay1_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay2_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay4_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 8 31 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 16 15 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 32 7 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 64 3 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 128 1 (by decide) (by decide)) ?_ hI
  exact fun _ hI => LIY.seq hdi hsi hwf hw hd (yscale_ok hd) (fun _ hI => hI.epi) hI

theorem nttY_ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub nttAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

theorem nttInvY_ct : ConstantTime isa (inPlaceK nttInv).pre (inPlaceK nttInv).pub nttInvAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

theorem nttY_verified : Verified X86_64.target nttAvx2 (Spec.MlDsa.nttContract X86_64.abi) :=
  Verified.of_correct nttY_correct nttY_ct (by
    mldsa_implies [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

theorem nttInvY_verified : Verified X86_64.target nttInvAvx2 (Spec.MlDsa.nttInvContract X86_64.abi) :=
  Verified.of_correct nttInvY_correct nttInvY_ct (by
    mldsa_implies [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith
