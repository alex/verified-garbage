import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.MlKem.X86_64.VLay

/-!
# ML-DSA on x86-64: the layers of the NTT and its inverse with `len ≥ 4`

For any butterfly code `bf` that does what `op` does to the doublewords of two
registers (`VBflyOk`), and any block of the specification whose butterflies do
`op` (`BlkOk`): four butterflies of a block (`vstep`), the `len / 4` of them
of a block (`vblock_ok`), and the `128 / len` blocks of a layer (`vlay_ok`),
on the polynomial at `fP`, with the zetas from the table at `sP`.
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (XOnly xmm_setXmm ifp ifn sel sel_lt sel_zero add_ofNat_zero Keep wp_countdown
  GOnly wp_rcxLoop sx1 sx16)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)

/-- Runs a block of general-purpose and SSE instructions. -/
syntax "vrund" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vrund) => `(tactic| vrund [])
  | `(tactic| vrund [$ls,*]) => `(tactic| vrunm [ea_atD, $ls,*])

/-- `GOnly` of a chain of `setReg` and `setFlags`. -/
macro "gonlyd" : tactic => `(tactic| exact ⟨⟨fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false], rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem gonly_vconsts {rs : List Reg} {s s' : State} (h : GOnly rs s s') (hc : VConsts s) : VConsts s' :=
  ⟨by rw [h.xmm]; exact hc.q, by rw [h.xmm]; exact hc.qinv⟩

/-- The code `bf` of four butterflies does what `op` does to each pair of
doublewords of `xmm0` and `xmm1`, with the zetas in `xmm13` (and `xmm12`),
leaving the results in `xmm0` and `xmm3`. -/
def VBflyOk (bf : List Instr) (op : Zq → Zq → Zq → Zq × Zq) : Prop :=
  ∀ s : State, VConsts s → ∀ x y ζ : Nat → Zq, DLanes (s.xmm .xmm0) x → DLanes (s.xmm .xmm1) y →
    ZLanes (s.xmm .xmm13) ζ → ZOdd (s.xmm .xmm13) (s.xmm .xmm12) →
    WP isa (.block bf) s fun s' => DLanes (s'.xmm .xmm0) (fun i => (op (x i) (y i) (ζ i)).1) ∧
      DLanes (s'.xmm .xmm3) (fun i => (op (x i) (y i) (ζ i)).2) ∧
      XOnly [.xmm1, .xmm2, .xmm4, .xmm0, .xmm3] s s'

theorem vbfly_spec : VBflyOk vbfly (fun x y z => (x + z * y, x - z * y)) :=
  fun _ hc _ _ _ hx hy hz ho => vbfly_ok hc hx hy hz ho

theorem vibfly_spec : VBflyOk vibfly (fun x y z => (x + y, z * (y - x))) :=
  fun _ hc _ _ _ hx hy hz ho => vibfly_ok hc hx hy hz ho

/-! ## A block -/

theorem f_in {rs : List Region} {fP : Addr} (hw : pR fP ∈ rs) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions rs (coeffAddr fP j) 16 :=
  ⟨_, hw, pR_contains fP hj⟩

theorem tab_in {rs : List Region} {sP : Addr} (hw : pR sP ∈ rs) {k : Nat} (hk : k + 4 ≤ 256) :
    InRegions rs (coeffAddr sP k) 16 :=
  ⟨_, hw, pR_contains sP hk⟩

/-- The facts a block keeps. -/
structure BInv (fP : Addr) (s₀ s : State) : Prop where
  keep : Keep [.r8, .rcx, .rdx, .rax] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem
  consts : VConsts s
  mxcsr : s.mxcsr = s₀.mxcsr

theorem BInv.trans {fP : Addr} {s₁ s₂ s₃ : State} (h₁ : BInv fP s₁ s₂) (h₂ : BInv fP s₂ s₃) : BInv fP s₁ s₃ :=
  ⟨(h₁.keep.trans h₂.keep).mono (by simp), h₁.frame.trans h₂.frame, h₂.consts, h₂.mxcsr.trans h₁.mxcsr⟩

/-! ## Four butterflies -/

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

/-- The body of the loop over the vectors of a block. -/
abbrev vbody (bf : List Instr) (len : Nat) : List Instr :=
  [.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx (4 * len))] ++ bf ++
    [.movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx (4 * len)) .xmm3, .alu .add .rdx (.imm 16)] ++
    [.alu .sub .rcx (.imm 1)]

theorem vstep {fP : Addr} {len st u k : Nat} (hl : 0 < len) (hs : st + 2 * len ≤ 256) (hu : 4 * u + 4 ≤ len)
    {G : Poly} {s : State} (hc : VConsts s) (hz : ZLanes (s.xmm .xmm13) (fun _ => zetas k))
    (ho : ZOdd (s.xmm .xmm13) (s.xmm .xmm12))
    (hdx : s.gpr .rdx = coeffAddr fP (st + 4 * u)) (hS : PolyIs s.mem fP (blk G len k st (4 * u)))
    (hw : pR fP ∈ s.wr) :
    WP isa (.block (vbody bf len)) s fun s' =>
      PolyIs s'.mem fP (blk G len k st (4 * (u + 1))) ∧ s'.gpr .rdx = coeffAddr fP (st + 4 * (u + 1)) ∧
        Frame [pR fP] s.mem s'.mem ∧ VConsts s' ∧ s'.xmm .xmm13 = s.xmm .xmm13 ∧
        s'.xmm .xmm12 = s.xmm .xmm12 ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : st + 4 * u + 4 ≤ 256 := by omega
  have j1 : st + 4 * u + len + 4 ≤ 256 := by omega
  have a1 : coeffAddr fP (st + 4 * u) + BitVec.ofNat 64 (4 * len) = coeffAddr fP (st + 4 * u + len) :=
    coeffAddr_add _ _ _
  have r0 : InRegions (s.rd ++ s.wr) (coeffAddr fP (st + 4 * u)) 16 := f_in (List.mem_append_right _ hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (coeffAddr fP (st + 4 * u + len)) 16 := f_in (List.mem_append_right _ hw) j1
  have w0 := f_in hw j0
  have w1 := f_in hw j1
  rw [vbody, List.append_assoc, List.append_assoc, WP.block_append_iff]
  vrund [hdx, a1, r0, r1]
  rw [WP.block_append_iff]
  have hx := dlanes_load hS j0
  have hy := dlanes_load hS j1
  refine WP.mono (hbf _ ((hc.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _)
    (fun e => (blk G len k st (4 * u))[st + 4 * u + e]!) (fun e => (blk G len k st (4 * u))[st + 4 * u + len + e]!)
    (fun _ => zetas k) (by rw [xmm_setXmm, xmm_setXmm]; exact hx) (by rw [xmm_setXmm]; exact hy)
    (by rw [xmm_setXmm, xmm_setXmm]; exact hz) (by rw [xmm_setXmm, xmm_setXmm, xmm_setXmm, xmm_setXmm]; exact ho))
    fun s2 ⟨l0, l3, o2⟩ => ?_
  have c2 := xonly_vconsts o2 ((hc.setXmm (by decide) (by decide) _).setXmm (by decide) (by decide) _) (by decide)
    (by decide)
  have g2 : s2.gpr = s.gpr := o2.gpr
  have m2 : s2.mem = s.mem := o2.mem
  have e2 : s2.rd = s.rd ∧ s2.wr = s.wr := ⟨o2.rd, o2.wr⟩
  have x2 : s2.mxcsr = s.mxcsr := o2.mxcsr
  have z2 : s2.xmm .xmm13 = s.xmm .xmm13 := by rw [o2.xmm _ (by decide), xmm_setXmm, xmm_setXmm]; rfl
  have z2' : s2.xmm .xmm12 = s.xmm .xmm12 := by rw [o2.xmm _ (by decide), xmm_setXmm, xmm_setXmm]; rfl
  vrund [g2, m2, e2.1, e2.2, hdx, a1, w0, w1, x2]
  refine ⟨?_, ?_, ?_, ⟨c2.q, c2.qinv⟩, z2, z2', ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · refine polyIs_write2 hS j0 j1 (by omega) l0 l3 fun i hi => ?_
    rw [show 4 * (u + 1) = 4 * u + 4 by omega, hblk.add, hblk.get _ _ _ _ _ hl (by omega)
      (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    by_cases c1 : st + 4 * u ≤ i ∧ i < st + 4 * u + 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c1), ite_eq_left_of_eq_true _ _ (eq_true c1),
        show st + 4 * u + (i - (st + 4 * u)) = i by omega,
        show st + 4 * u + len + (i - (st + 4 * u)) = i + len by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c1), ite_eq_right_of_eq_false _ _ (eq_false c1)]
      by_cases c2 : st + 4 * u + len ≤ i ∧ i < st + 4 * u + len + 4
      · rw [ite_eq_left_of_eq_true _ _ (eq_true c2), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
          show st + 4 * u + (i - (st + 4 * u + len)) = i - len by omega,
          show st + 4 * u + len + (i - (st + 4 * u + len)) = i by omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false c2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_add,
      show st + 4 * u + 4 = st + 4 * (u + 1) by omega]
  · exact frame_write2 (Frame.refl _ _) j0 j1 _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

/-- The code of a block of a layer with `len ≥ 4`. -/
abbrev vblk (bf : List Instr) (len : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block (vzeta 0 ++ [.alu .add .r8 (.imm dz)]))
    (.seq (VG.Impl.MlKem.X86_64.rcxLoop (len / 4) ([.movdquLoad .xmm0 (at_ .rdx 0),
        .movdquLoad .xmm1 (at_ .rdx (4 * len))] ++
        bf ++ [.movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx (4 * len)) .xmm3,
          .alu .add .rdx (.imm 16)]))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (4 * len))), .alu .sub .rax (.imm 1)]))

theorem vblock_ok {fP sP : Addr} {len st kz : Nat} (h4 : 4 ≤ len) (hl4 : len % 4 = 0) (hl : len ≤ 128)
    (hs : st + 2 * len ≤ 256) (hkz : kz + 4 ≤ 256) (dz : BitVec 32) {G : Poly} {s : State} (hc : VConsts s)
    (hdx : s.gpr .rdx = coeffAddr fP st) (h8r : s.gpr .r8 = coeffAddr sP kz) (hS : PolyIs s.mem fP G)
    (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (vblk bf len dz) s fun s' => PolyIs s'.mem fP (blk G len kz st len) ∧
      s'.gpr .rdx = coeffAddr fP (st + 2 * len) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      s'.gpr .rax = s.gpr .rax - 1 ∧ s'.zf = some (s.gpr .rax - 1 == 0) ∧ BInv fP s s' := by
  -- the zeta
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (vzeta_ok 0 (k := kz) (fun j _ => by rw [sel_zero]; omega) h8r
    (tab_in (List.mem_append_right _ hw) hkz) hT) fun s1 ⟨z1, zo1, o1⟩ => ?_
  have g1 : s1.gpr = s.gpr := o1.gpr
  refine WP.mono (Q := fun (s2 : State) => s2.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧
      GOnly [.r8] s1 s2)
    (by vrund [g1]; gonlyd)
    fun s2 ⟨h82, o2⟩ => ?_
  have c2 := gonly_vconsts o2 (xonly_vconsts o1 hc (by decide) (by decide))
  have z2 : ZLanes (s2.xmm .xmm13) (fun _ => zetas kz) := by
    rw [o2.xmm]; intro i hi; rw [z1 i hi]; dsimp only; rw [sel_zero, Nat.add_zero]
  have zo2 : ZOdd (s2.xmm .xmm13) (s2.xmm .xmm12) := by rw [o2.xmm]; exact zo1
  have dx2 : s2.gpr .rdx = coeffAddr fP st := by rw [o2.keep.gpr (by decide), g1, hdx]
  have hw2 : pR fP ∈ s2.wr := by rw [o2.keep.2.2, o1.wr]; exact hwf
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  refine WP.seq (WP.mono (wp_rcxLoop (N := len / 4) (by omega) (by omega)
    (fun u w => PolyIs w.mem fP (blk G len kz st (4 * u)) ∧ w.gpr .rdx = coeffAddr fP (st + 4 * u) ∧
      VConsts w ∧ w.xmm .xmm13 = s2.xmm .xmm13 ∧ w.xmm .xmm12 = s2.xmm .xmm12 ∧ Keep [.rcx, .rdx] s2 w ∧
      Frame [pR fP] s2.mem w.mem ∧ w.mxcsr = s2.mxcsr)
    (fun w o hc => ⟨by rw [hblk.zero, o.mem, m2]; exact hS, by rw [o.keep.gpr (by decide), dx2]; rfl,
      gonly_vconsts o c2, by rw [o.xmm], by rw [o.xmm], o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _,
      o.mxcsr⟩)
    (fun u hu w ⟨hS', hdx', hc', hz', hzo', hk', hf', hx'⟩ => WP.mono (vstep hbf hblk (by omega) hs (by
        have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hl4); omega) hc' (by rw [hz']; exact z2)
        (by rw [hz', hzo']; exact zo2) hdx' hS' (by rw [hk'.2.2]; exact hw2))
      fun w' ⟨hS'', hdx'', hf'', hc'', hz'', hzo'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', by rw [hz'', hz'], by rw [hzo'', hzo'], (hk'.trans hk'').mono (by simp),
          hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩)) fun w ⟨hS3, hdx3, hc3, _, _, hk3, hf3, hx3⟩ => ?_)
  rw [show 4 * (len / 4) = len from Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl4)] at hS3 hdx3
  have hax : w.gpr .rax = s.gpr .rax := by rw [hk3.gpr (by decide), o2.keep.gpr (by decide), g1]
  have h8w : w.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz := by rw [hk3.gpr (by decide), h82]
  vrund [hdx3, sx_ofNat (show 4 * len < 2 ^ 31 by omega), hax, h8w]
  refine ⟨hS3, by rw [coeffAddr_add, show st + len + len = st + 2 * len by omega], ?_⟩
  have k1 : Keep [.r8, .rcx, .rdx, .rax] s w :=
    (Keep.trans (⟨fun r _ => by rw [g1], o1.rd, o1.wr⟩ : Keep [] s s1) (o2.keep.trans hk3)).mono (by simp)
  refine ⟨⟨fun r hr => ?_, k1.2.1, k1.2.2⟩, by rw [← m2]; exact hf3,
    ⟨by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact hc3.q,
      by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact hc3.qinv⟩,
    by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [hx3, o2.mxcsr, o1.mxcsr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  exact k1.gpr (by simp [hr])

/-! ## A layer -/

theorem vlay_ok {fP sP : Addr} {len k : Nat} (hlen : len ∈ [4, 8, 16, 32, 64, 128]) (dz : BitVec 32)
    (zi : Nat → Nat) (hz0 : zi 0 = k) (hzi : ∀ c < 128 / len, zi c + 4 ≤ 256)
    (hstep : ∀ c < 128 / len, coeffAddr sP (zi c) + BitVec.signExtend 64 dz = coeffAddr sP (zi (c + 1)))
    {F : Poly} {s : State} (hc : VConsts s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (vlay bf len k dz) s fun s' => PolyIs s'.mem fP (layF blk F len zi (128 / len)) ∧
      BInv fP s s' := by
  have hl : 4 ≤ len ∧ len % 4 = 0 ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
      128 / len ≤ 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h4, hl4, hl128, hcov, hpos, h32⟩ := hl
  have hk : k + 4 ≤ 256 := hz0 ▸ hzi 0 hpos
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧ w.gpr .r8 = coeffAddr sP k ∧
      w.gpr .rax = BitVec.ofNat 64 (128 / len) ∧ GOnly [.rdx, .r8, .rax] s w)
    (by
      simp only [leaR]
      vrund [sx_ofNat (show 4 * k < 2 ^ 31 by omega), hsi, hdi]
      refine ⟨?_, by gonlyd⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega) fun w ⟨hdx, h8r, hax, o⟩ => ?_)
  have hwf' : pR fP ∈ w.wr := by rw [o.keep.2.2]; exact hwf
  have hw' : pR sP ∈ w.wr := by rw [o.keep.2.2]; exact hw
  refine WP.mono (wp_countdown (cnt := .rax) (N := 128 / len) (by omega) hpos
    (fun c u => PolyIs u.mem fP (layF blk F len zi c) ∧ u.gpr .rdx = coeffAddr fP (2 * len * c) ∧
      u.gpr .r8 = coeffAddr sP (zi c) ∧ BInv fP w u ∧ Tab zmTab u.mem sP 256)
    (fun c hc u ⟨hS', hdx', h8', hb', hT'⟩ _ => ?_) (fun u h => h)
    ⟨by rw [o.mem]; exact hS, by rw [hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [h8r, hz0], ⟨Keep.refl _ _, Frame.refl _ _, gonly_vconsts o hc, rfl⟩, by rw [o.mem]; exact hT⟩ hax)
    fun u ⟨hS', _, _, hb', _⟩ => ⟨hS', ⟨(o.keep.trans hb'.keep).mono (by simp),
      by rw [← o.mem]; exact hb'.frame, hb'.consts, by rw [hb'.mxcsr, o.mxcsr]⟩⟩
  have hs : 2 * len * c + 2 * len ≤ 256 := by
    have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (vblock_ok hbf hblk h4 hl4 hl128 hs (hzi c hc) dz hb'.consts hdx' h8' hS' hT'
    (by rw [hb'.keep.2.2]; exact hwf') (by rw [hb'.keep.2.2]; exact hw'))
    fun u' ⟨hS'', hdx'', h8'', hax'', hzf'', hb''⟩ =>
      ⟨⟨by rw [layF, foldl_range_succ]; exact hS'', by rw [hdx'', Nat.mul_succ],
        by rw [h8'', h8', hstep c hc], hb'.trans hb'',
        hT'.frame hb''.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)⟩, hax'', hzf''⟩

end

end VG.Proof.MlDsa.X86_64.Arith
