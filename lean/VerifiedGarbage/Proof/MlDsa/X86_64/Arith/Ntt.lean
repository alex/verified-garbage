import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-DSA on x86-64: `vg_mldsa_ntt`

ML-KEM's `withMxcsr` runs its code from any MXCSR and keeps what it does
(`withMxcsr_ok`); the prologue leaves the table of zetas in `scratch` and the
constants (`vpro_ok`), each layer is `nttLayer` (`vlay_ok`, `vlay2_ok`,
`vlay1_ok`), and the eight layers are `NTT` (`ntt_eq_layers`). `LI`, `vpro_ok`
and `inPlaceSat` serve `NTT⁻¹` too.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of withMxcsr_ok mxR mx_sub xmm_setXmm
  GOnly add_ofNat_zero sel)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas ntt)

/-! ## The prologue -/

/-- A table of 256 `u32`s `t k`, stored at `sP` (in `r`), two at a time
through `r9`. -/
theorem dwordTab_ok (t : Nat → Nat) (ht : ∀ k, t k < 2 ^ 32) {r : Reg} (hr : r ≠ .r9) {sP : Addr} {s : State}
    (hsi : s.gpr r = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block (dwordTab t 256 r)) s fun s' => Tab t s'.mem sP 256 ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9] s s' ∧ s'.mxcsr = s.mxcsr ∧ s'.xmm = s.xmm := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 128) (fun i w =>
      Tab t w.mem sP (2 * i) ∧ Frame [pR sP] s.mem w.mem ∧
        Keep [.r9] s w ∧ w.mxcsr = s.mxcsr ∧ w.xmm = s.xmm)
    (fun i w hi ⟨hT, hf, hk, hm, hx⟩ => ?_) 128 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega), Frame.refl _ _, Keep.refl _ _, rfl, rfl⟩)
    fun w ⟨hT, hf, hk, hm, hx⟩ => ⟨hT, hf, hk, hm, hx⟩
  have hsi' : w.gpr r = sP := by
    rw [hk.gpr (by simp only [List.mem_singleton]; exact hr), hsi]
  have w0 : InRegions w.wr (sP + BitVec.ofNat 64 (8 * i)) 8 :=
    ⟨_, by rw [hk.2.2]; exact hw, Offset.contains_base sP (by omega) (by omega)⟩
  have hV : ∀ e < 2, (BitVec.ofNat 64 (t (2 * i) + 2 ^ 32 * t (2 * i + 1))).extractLsb' (32 * e) 32 =
      BitVec.ofNat 32 (t (2 * i + e)) := fun e he => by
    apply BitVec.eq_of_toNat_eq
    have h0 := ht (2 * i)
    have h1 := ht (2 * i + 1)
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_zero]; omega
    · simp only [Nat.mul_one]; omega
  vrund [hsi', w0, hr]
  generalize BitVec.ofNat 64 (t (2 * i) + 2 ^ 32 * t (2 * i + 1)) = V at hV ⊢
  refine ⟨fun k hk' => ?_, hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base sP (by omega) (by omega)),
    ⟨fun r hr => ?_, hk.2.1, hk.2.2⟩, hm, hx⟩
  · by_cases h : 2 * i ≤ k
    · rw [coeffAt_eq, coeffAddr, show sP + BitVec.ofNat 64 (4 * k) =
          sP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (4 * (k - 2 * i)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact congrArg _ (congrArg _ (by omega)),
        show 32 = 8 * 4 from rfl, readW_writeW_inside _ _ _ (by omega) (by decide),
        show 8 * (4 * (k - 2 * i)) = 32 * (k - 2 * i) by omega, hV _ (by omega),
        show 2 * i + (k - 2 * i) = k by omega]
    · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep sP (by omega) (by omega) (by omega)) (by decide)]
      exact hT k (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
    exact hk.1 r (by simp [hr])

theorem vconsts_ok (s : State) :
    WP isa (.block vconsts) s fun s' => VConsts s' ∧ Keep [.rax] s s' ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr := by
  simp only [vconsts]
  vrund
  refine ⟨⟨?_, ?_⟩, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true]; decide
  · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]; decide
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]

/-- The table of zetas and the constants. -/
theorem vpro_ok {sP : Addr} {s : State} (hsi : s.gpr .rsi = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block vpro) s fun s' => Tab zmTab s'.mem sP 256 ∧ VConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9, .rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [vpro, WP.block_append_iff]
  refine WP.mono (dwordTab_ok zmTab (fun k => Nat.lt_trans (zmTab_lt k) (by decide)) (by decide) hsi hw)
    fun s1 ⟨hT, hf, k1, x1, _⟩ => WP.mono (vconsts_ok s1) fun s2 ⟨hc, k2, m2, x2⟩ =>
      ⟨by rw [m2]; exact hT, hc, by rw [m2]; exact hf, (k1.trans k2).mono (by simp), by rw [x2, x1]⟩

/-! ## The layers -/

/-- Between the layers: the polynomial `F` at `fP`, the table at `sP`, and
the constants. -/
structure LI (fP sP : Addr) (s₀ : State) (F : Poly) (s : State) : Prop where
  P : PolyIs s.mem fP F
  T : Tab zmTab s.mem sP 256
  c : VConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem

/-- The last layer. -/
theorem LI.last {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l : Prog isa}
    {F F' : Poly}
    (hl : ∀ s, VConsts s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F → Tab zmTab s.mem sP 256 →
      pR fP ∈ s.wr → pR sP ∈ s.wr → WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInv fP s s')
    {s : State} (hI : LI fP sP s₀ F s) : WP isa l s (LI fP sP s₀ F') :=
  WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩

/-- A layer, then `c`. -/
theorem LI.seq {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l c : Prog isa}
    {F F' : Poly} {Q : State → Prop}
    (hl : ∀ s, VConsts s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F → Tab zmTab s.mem sP 256 →
      pR fP ∈ s.wr → pR sP ∈ s.wr → WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInv fP s s')
    (hc : ∀ s, LI fP sP s₀ F' s → WP isa c s Q) {s : State} (hI : LI fP sP s₀ F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

theorem step_fwd (p : Addr) (a d : Nat) {dz : BitVec 32} (h : BitVec.signExtend 64 dz = BitVec.ofNat 64 (4 * d)) :
    coeffAddr p a + BitVec.signExtend 64 dz = coeffAddr p (a + d) := by
  rw [h, coeffAddr_add]

theorem step_bwd (p : Addr) (a d : Nat) {dz : BitVec 32}
    (h : BitVec.ofNat 64 (4 * d) + BitVec.signExtend 64 dz = 0) :
    coeffAddr p (a + d) + BitVec.signExtend 64 dz = coeffAddr p a := by
  rw [← coeffAddr_add, BitVec.add_assoc, h]; exact BitVec.add_zero _

/-- The block of `NTT`. -/
abbrev fwdBlk : Poly → Nat → Nat → Nat → Nat → Poly := fun f len k st t => blockN bfly f len (zetas k) st t

theorem nttLayer_eq (F : Poly) (len : Nat) :
    nttLayer F len = layF fwdBlk F len (fun c => 128 / len + c) (128 / len) := rfl

/-- A layer of `NTT` with `len ≥ 4`, whose first zeta is `zetas k`. -/
theorem fwdLay_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) (len k : Nat) (hlen : len ∈ [4, 8, 16, 32, 64, 128]) (hk : 128 / len = k)
    {F : Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (vlay vbfly len k 4) s fun s' => PolyIs s'.mem fP (nttLayer F len) ∧ BInv fP s s' := by
  rw [nttLayer_eq]
  exact vlay_ok vbfly_spec nttBlk_ok hlen 4 (fun c => 128 / len + c) (by rw [hk]; rfl)
    (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun c _ => step_fwd _ _ 1 (by decide)) hc hdi hsi hS hT hwf hw hd

theorem fwdLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr)
    (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 vbfly 64 0x50 8) s fun s' => PolyIs s'.mem fP (nttLayer F 2) ∧ BInv fP s s' := by
  have hs : ∀ e < 4, sel 0x50 e = e / 2 := by decide
  rw [nttLayer_eq, show 128 / 2 = 64 from rfl]
  exact vlay2_ok vbfly_spec nttBlk_ok 64 0x50 8 (fun c => 64 + c) (fun i => 64 + 2 * i) rfl
    (fun i _ => by omega) (fun i _ e he => by rw [hs e he]; omega)
    (fun i _ => (step_fwd _ _ 2 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd

theorem fwdLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : VConsts s) (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr)
    (hw : pR sP ∈ s.wr) :
    WP isa (vlay1 vbfly 128 0xE4 16) s fun s' => PolyIs s'.mem fP (nttLayer F 1) ∧ BInv fP s s' := by
  have hs : ∀ e < 4, sel 0xE4 e = e := by decide
  rw [nttLayer_eq, show 128 / 1 = 128 from rfl]
  exact vlay1_ok vbfly_spec nttBlk_ok 128 0xE4 16 (fun c => 128 + c) (fun i => 128 + 4 * i) rfl
    (fun i _ => by omega) (fun i _ e he => by rw [hs e he]; omega)
    (fun i _ => (step_fwd _ _ 4 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd

/-! ## `vg_mldsa_ntt` -/

theorem mx_sub' (sP : Addr) : Region.Sub (mxR sP) (pR sP) := mx_sub sP

/-- The regions of `scratch` within it, and `f`. -/
theorem frame_fs {fP sP : Addr} {m m' : Mem} {rs : List Region} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (pR fP) ∨ Region.Sub r (pR sP)) : Frame [pR fP, pR sP] m m' :=
  h.sub fun r hr => (hs r hr).elim (fun h => ⟨_, List.mem_cons_self .., h⟩)
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

/-- The code in `withMxcsr`, from its state `s1`: the prologue, then the
layers `l`, which leave `F`, then `NTT⁻¹`'s scaling or nothing. -/
theorem nttBody_ok {t : Poly → Poly} {s s1 : State} (hs : (inPlaceK t).pre s) {l : Prog isa} {G : Poly}
    (k1 : Keep [.rax, .r11] s s1) (f1 : Frame [mxR (s.gpr .rsi)] s.mem s1.mem)
    (hl : ∀ s2, LI (s.gpr .rdi) (s.gpr .rsi) s2 (polyAt s.mem (s.gpr .rdi)) s2 → s2.gpr .rdi = s.gpr .rdi →
      s2.gpr .rsi = s.gpr .rsi → pR (s.gpr .rdi) ∈ s2.wr → pR (s.gpr .rsi) ∈ s2.wr →
      WP isa l s2 fun s3 => LI (s.gpr .rdi) (s.gpr .rsi) s2 G s3) :
    WP isa (.seq (.block vpro) l) s1 fun s' =>
      PolyIs s'.mem (s.gpr .rdi) G ∧ Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
  have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
  have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _))
      ⟨hs.2.2.2.2.2, rfl⟩
  refine WP.seq (WP.mono (vpro_ok hsi1 (by rw [k1.2.2]; exact hw)) fun s2 ⟨hT, hc, hf2, k2, _⟩ => ?_)
  have hF2 : PolyIs s2.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hF1
  refine WP.mono (hl s2 ⟨hF2, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    (by rw [k2.gpr (by decide), hdi1]) (by rw [k2.gpr (by decide), hsi1])
    (by rw [k2.2.2, k1.2.2]; exact hwf) (by rw [k2.2.2, k1.2.2]; exact hw)) fun s3 hI => ⟨hI.P, ?_⟩
  refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans (frame_fs hI.frame ?_)) <;>
    intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
  exacts [.inr (mx_sub' _), .inr fun _ h => h, .inl fun _ h => h]

/-- `withMxcsr` around the body, and the ABI. -/
theorem mx_correct {t : Poly → Poly} {l : Prog isa} (s : State) (hs : (inPlaceK t).pre s)
    (hk : writesOnly [.rax, .rcx, .rdx, .r8, .r9] (.seq (.block vpro) l) = true)
    (hctl : ctlOk (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block vpro) l)) = true)
    (hk' : writesOnly [.rax, .rcx, .rdx, .r8, .r9, .r11]
      (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block vpro) l)) = true)
    (hl : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxR (s.gpr .rsi)] s.mem s1.mem →
      WP isa (.seq (.block vpro) l) s1 fun s' => PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem) :
    ∃ tr s', Exec isa (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block vpro) l)) s tr s' ∧
      abiPreserved s s' ∧ (inPlaceK t).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW := withMxcsr_ok (c := .seq (.block vpro) l) (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw
    hk (hl)
  obtain ⟨tr, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW hk'
  refine ⟨tr, s', he, abiPreserved_of_ctl hctl he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub' _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _)) hP

theorem ntt_correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.ntt s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine mx_correct s hs (by decide +kernel) (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    WP.mono (nttBody_ok hs k1 f1 (G := nttLens.foldl nttLayer (polyAt s.mem (s.gpr .rdi)))
      fun s2 hI hdi hsi hwf hw => ?_) fun s' ⟨hP, hf⟩ => ⟨by rw [ntt_eq_layers]; exact hP, hf⟩
  simp only [nttLens, List.foldl_cons, List.foldl_nil]
  refine LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 128 1 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 64 2 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 32 4 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 16 8 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 8 16 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay_ok hd 4 32 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LI.seq hdi hsi hwf hw hd (fwdLay2_ok hd) ?_ hI
  exact fun _ hI => LI.last hdi hsi hwf hw hd (fwdLay1_ok hd) hI

/-- The pointers and `rsp` are public. -/
theorem inPlace_agree {t : Poly → Poly} (s₁ s₂ : State) (_ : (inPlaceK t).pre s₁) (_ : (inPlaceK t).pre s₂)
    (hp : (inPlaceK t).pub s₁ s₂) : X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2]

theorem ntt_ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub Impl.MlDsa.X86_64.Arith.ntt :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def inPlaceSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.ntt (Spec.MlDsa.nttContract X86_64.abi) :=
  Verified.of_correct ntt_correct ntt_ct (by
    mldsa_implies [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith
