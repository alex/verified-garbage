import VerifiedGarbage.Proof.Bignum.X86_64.PdCode
import VerifiedGarbage.Proof.Bignum.X86_64.PdCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-!
# `vg_rsa_public_precomputed` on x86-64: constant time but for `pre` and `e`

Every piece's addresses and branches depend only on the pointers, the
lengths, `pre` and `e`: the load and the checks of `pre` (`pdLoad_ct`),
`rest` (`pdRest_ct`), and the whole function (`pdCode_constantTime`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-! ## `rest` -/

/-- The public data of `rest`: the working space, `k`, the pointers, `e`
and the values `N` and `R` in the arrays. -/
structure DPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  ep : Addr
  ip : Addr
  len : Nat
  eb : List Byte
  N : Nat
  R : Nat

/-- `pdRest_ok`'s hypotheses. -/
def DRel (p : DPub) (s : State) : Prop :=
  ∃ xb, PdPre s p.B p.Z p.k p.op p.ep p.ip p.len p.eb xb p.N p.R

/-- From `σ`, at `rest`'s start, to `t`: what changed, and the mask. -/
def DG (p : DPub) (xb : List Byte) (σ t : State) : Prop :=
  PdPre σ p.B p.Z p.k p.op p.ep p.ip p.len p.eb xb p.N p.R ∧ Frm p.B (pdAll ((p.k + 7) / 8)) σ.mem t.mem ∧
    Keep mmRegs σ t ∧ word t.mem p.B (8 * sMask) = mask (decide (Spec.Rsa.os2ip xb < p.N))

theorem PdPre.mem {s t : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte}
    {N R : Nat} (h : PdPre s B Z k op ep ip L eb xb N R) (hm : t.mem = s.mem) {regs : List Reg} (kp : Keep regs s t)
    (hr : .rdi ∉ regs) : PdPre t B Z k op ep ip L eb xb N R :=
  { scr := h.scr.congr kp.2.2, rdi := (kp.gpr hr).trans h.rdi, z := h.z, k1 := h.k1, k2 := h.k2,
    hO := hm ▸ h.hO, hK := hm ▸ h.hK, hE := hm ▸ h.hE, hL := hm ▸ h.hL, hIn := hm ▸ h.hIn, hW := hm ▸ h.hW,
    hb := hm ▸ h.hb, n := hm ▸ h.n, r := hm ▸ h.r, odd := h.odd, n1 := h.n1, rlt := h.rlt,
    x := h.x.congrK (by rw [hm]; exact InScr.refl _ _ _) kp, e := h.e.congrK (by rw [hm]; exact InScr.refl _ _ _) kp,
    xl := h.xl, el := h.el, L1 := h.L1, L2 := h.L2, out := fun j hj => by rw [kp.2.2]; exact h.out j hj,
    outSep := h.outSep }

theorem DG.step {p : DPub} {xb : List Byte} {σ t t' : State} (h : DG p xb σ t)
    (hf : Frm p.B (pdAll ((p.k + 7) / 8)) t.mem t'.mem) (k : Keep mmRegs t t')
    (hm : word t'.mem p.B (8 * sMask) = word t.mem p.B (8 * sMask)) : DG p xb σ t' :=
  ⟨h.1, h.2.1.trans hf, (h.2.2.1.trans k).mono (by decide), hm.trans h.2.2.2⟩

theorem DG.fixed {p : DPub} {xb : List Byte} {σ t : State} (h : DG p xb σ t) : Fixed p.B σ.mem t.mem :=
  Fixed.of_frm h.2.1 (pdAll_fixed _)

theorem DG.inScr {p : DPub} {xb : List Byte} {σ t : State} (h : DG p xb σ t) : InScr p.B p.Z σ.mem t.mem :=
  InScr.of_frm h.2.1 fun r hr => (pdAll_le _ r hr).trans h.1.z

/-- After the input's registers. -/
def DIn (p : DPub) (s : State) : Prop :=
  DRel p s ∧ s.gpr .rsi = p.ip ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = off p.B (slot ((p.k + 7) / 8) aX)

/-- The input leaks the same in runs with the same public data. -/
theorem pdIn_ct : RelCT isa (Two DRel) (seqs pdIn) (Two fun (p : DPub) s => SR ⟨p.B, p.Z, ((p.k + 7) / 8)⟩ s) := by
  unfold pdIn
  refine RelCT.seq (two_piece (Ψ := DIn) [.rdi] (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) (by taint_decide) ?_) ?_
  · rintro p s ⟨xb, h⟩
    have hn := h.scr.nowrap
    have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := h.z
    obtain ⟨g0, g8⟩ := slot0_ge ((p.k + 7) / 8)
    refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = p.ip ∧
        t.gpr .rcx = BitVec.ofNat 64 p.k ∧ t.gpr .rbx = off p.B (slot ((p.k + 7) / 8) aX) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sIn) (by unfold sIn sFn; omega),
        h.scr.ld (d := 8 * sK) (by unfold sK sFn; omega), h.scr.ld (d := 8 * sArr aX) (by unfold sArr aX; omega),
        h.hIn, h.hK, h.hb aX (by decide)]) rfl)
      fun t ⟨⟨hsi, hcx, hbx, hm⟩, k⟩ => ⟨⟨xb, h.mem hm k (by decide)⟩, hsi, hcx, hbx⟩
  rw [seqs_one]
  refine two_piece [.rsi, .rcx, .rbx] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_
  rintro p s ⟨⟨xb, h⟩, hsi, hcx, hbx⟩
  have hk1 := h.k1
  have hk2 := h.k2
  have hn := h.scr.nowrap
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := h.z
  have hn' : p.B.toNat + slot ((p.k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hw : 2 ≤ ((p.k + 7) / 8) := by show 2 ≤ (p.k + 7) / 8; omega
  refine WP.mono (loadArr_ok h.scr (by decide) h.z h.x h.xl (by omega) (by omega) hsi hcx hbx)
    fun t ⟨_, ha, k⟩ => ⟨h.scr.congr k.2.2, (k.gpr (by decide)).trans h.rdi, h.z,
      hw, show ((p.k + 7) / 8) < 2 ^ 31 by show (p.k + 7) / 8 < 2 ^ 31; omega,
      by rw [ha.hslot (by decide)]; exact h.hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega)]; exact h.hb j hj, ?_⟩
  rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega),
    ← wv_mod64 _ _ _ (show 1 ≤ ((p.k + 7) / 8) by omega), Nat.mod_mod_of_dvd _ (by decide), h.n, h.odd]

/-- After the setup, for `-m⁻¹ = q.2`. -/
def DA (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ SetupOut t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 q.1.N (Spec.Rsa.os2ip xb) ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aR2) ((q.1.k + 7) / 8) = q.1.R

/-- The setup leaks the same in runs with the same public data. -/
theorem pdSetup_ct : RelCT isa (Two DRel) (seqs (pdIn ++ restSteps)) (Two DA) := by
  refine two_post (Ψ := fun p t => ∃ mi, DA (p, mi) t)
    (RelCT.seqs_append (by simp [pdIn]) (by simp [restSteps]) (RelCT.seq pdIn_ct (two_map (fun p : DPub => (⟨p.B, p.Z, ((p.k + 7) / 8)⟩ : RPub)) (fun _ _ h => h) setupRest_ct))) ?_ |>.mono
      (fun _ _ h => h) fun _ _ h => two_bind (fun p t₁ t₂ H₁ H₂ => ?_) h
  · rintro p s ⟨xb, h⟩
    exact WP.mono (pdSetup_ok h) fun t ⟨mi, so, f, k, hR⟩ => ⟨mi, xb, s, ⟨h, f, k, so.mask⟩, so, hR⟩
  · obtain ⟨mi₁, h₁⟩ := H₁
    obtain ⟨mi₂, h₂⟩ := H₂
    have ⟨xb₁, σ₁, g₁, so₁, _⟩ := h₁
    have ⟨xb₂, σ₂, g₂, so₂, _⟩ := h₂
    have : 64 ≤ p.k := g₁.1.k1
    obtain rfl := so_minv so₁ so₂ g₁.1.odd (show 1 ≤ ((p.k + 7) / 8) by show 1 ≤ (p.k + 7) / 8; omega)
    exact ⟨(p, mi₁), h₁, h₂⟩

/-- `rest`'s public data with `-m⁻¹`. -/
abbrev DPub.L (q : DPub × BitVec 64) : Lay := ⟨q.1.B, q.1.Z, ((q.1.k + 7) / 8), q.2⟩

/-- After `X := input R`. -/
def DB (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ Good t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 ∧ wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aN) ((q.1.k + 7) / 8) = q.1.N ∧
    ((word t.mem q.1.B (slot ((q.1.k + 7) / 8) aN)).toNat * q.2.toNat + 1) % 2 ^ 64 = 0 ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aXm) ((q.1.k + 7) / 8) < q.1.N ∧ wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aOne) ((q.1.k + 7) / 8) = 1

theorem arrays_pdAll {B : Addr} {w : Nat} {m m' : Mem} (h : Arrays B w [aAcc, aTmp, aXm] m m') :
    Frm B (pdAll w) m m' :=
  Frm.of_arrays h (by simp [pdAll, pExpRanges, pBitRanges, bitRanges])

/-- `X := input R` leaks the same in runs with the same public data. -/
theorem pdMm_ct : RelCT isa (Two DA) (M.mm aXm aX aR2) (Two DB) := by
  refine two_post (two_map DPub.L (fun _ _ ⟨_, σ, g, so, _⟩ => ⟨so.good, g.1.z⟩)
    (M.ct (by unfold MmUse; decide))) ?_
  rintro q t ⟨xb, σ, g, so, hR⟩
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hn : q.1.B.toNat + slot ((q.1.k + 7) / 8) 8 ≤ 2 ^ 64 := by have := g.1.scr.nowrap; have := g.1.z; omega
  refine WP.mono (mmN_ok M (o := aXm) (a := aX) (b := aR2) so.good g.1.z (by omega)
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) so.n so.inv (by rw [hR]; exact g.1.rlt)) fun t' ⟨hg, hn', hinv, hlt, _, ha, k⟩ =>
    ⟨xb, σ, g.step (arrays_pdAll ha) k (ha.hslot (by decide)), hg, hn', hinv, hlt, ?_⟩
  rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact so.one

/-- The exponentiation's public data. -/
def DPub.E (q : DPub × BitVec 64) : EPub := ⟨DPub.L q, q.1.N, q.1.ep, q.1.len, q.1.eb⟩

theorem db_pre {q : DPub × BitVec 64} {t : State} (h : DB q t) : PExpPre (DPub.E q) t := by
  obtain ⟨xb, σ, g, hg, hn, hinv, hlt, -⟩ := h
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hL2 := g.1.L2
  have hR := VG.Proof.Bignum.coprime_pow2 g.1.odd (64 * ((q.1.k + 7) / 8))
  obtain ⟨x, hx⟩ := exists_mont hR g.1.n1 (wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aXm) ((q.1.k + 7) / 8))
  have he := g.1.e.congrK g.inScr g.2.2.1
  exact ⟨_, x, ⟨hg, hn, hinv, rfl⟩, ⟨g.1.z, show 2 ≤ ((q.1.k + 7) / 8) by omega,
    show ((q.1.k + 7) / 8) < 2 ^ 31 by omega, hR, hlt, hx⟩,
    (g.fixed sE (by decide)).trans g.1.hE, (g.fixed sElen (by decide)).trans g.1.hL, g.1.L1,
    src_esrc he g.1.el (show q.1.len < 2 ^ 31 by omega)⟩

/-- After the exponentiation. -/
def DC (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ X x, DG q.1 xb σ t ∧ ExpCtx t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 q.1.N X ∧
    YSt t.mem q.1.B ((q.1.k + 7) / 8) q.1.N x (Spec.Rsa.os2ip q.1.eb) ∧ wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aOne) ((q.1.k + 7) / 8) = 1

theorem pExpRanges_pdAll (w : Nat) : ∀ r ∈ pExpRanges w, r ∈ pdAll w :=
  fun _ hr => List.mem_append_right _ hr

/-- The exponentiation leaks the same in runs that agree on `e`. -/
theorem pdExp_ct : RelCT isa (Two DB) (Precomputed.expLoop M.mm) (Two DC) := by
  refine two_post ((two_map DPub.E (fun _ _ h => db_pre h) pExpLoop_ct).mono (fun _ _ h => h)
    fun _ _ _ => trivial) ?_
  rintro q t h
  obtain ⟨X, x, hc, hf, he, hlen, hL1, hsrc⟩ := db_pre h
  obtain ⟨xb, σ, g, -, -, -, -, hone⟩ := h
  have hn : q.1.B.toNat + slot ((q.1.k + 7) / 8) 8 ≤ 2 ^ 64 := by have := g.1.scr.nowrap; have := g.1.z; omega
  refine WP.mono (pExpLoop_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 he hlen hsrc.1 hL1
    hsrc.2.1 hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2) fun t' ⟨hc', hy, f₀, k⟩ => ?_
  have f : Frm q.1.B (pExpRanges ((q.1.k + 7) / 8)) t.mem t'.mem := f₀
  refine ⟨xb, σ, X, x, g.step (f.mono (pExpRanges_pdAll _)) k
      (f.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (by unfold sMask sFn; omega)), hc', hy, ?_⟩
  rw [f.wv_eq (fun r hr => by
      have := hdr_lt_slot ((q.1.k + 7) / 8) aOne (show 31 < 32 by decide)
      have := slot_sep (w := ((q.1.k + 7) / 8)) (show aOne ≠ aAcc by decide)
      have := slot_sep (w := ((q.1.k + 7) / 8)) (show aOne ≠ aTmp by decide)
      have := slot_sep (w := ((q.1.k + 7) / 8)) (show aOne ≠ aY by decide)
      simp only [pExpRanges, pBitRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sI, sV, sBit, Precomputed.sStarted, sFn] at * <;> omega)
      (by have := slot_le (w := ((q.1.k + 7) / 8)) (show aOne < 8 by decide); omega)]
  exact hone

/-- After `finish`. -/
def DD (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ Good t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2

/-- `finish` leaks the same in runs that agree on `e`. -/
theorem pdFinish_ct : RelCT isa (Two DC) (Precomputed.finish M.mm) (Two DD) := by
  refine two_post (two_map (fun q => (⟨DPub.L q, q.1.N, Spec.Rsa.os2ip q.1.eb⟩ : FPub))
    (fun q _ ⟨_, _, X, x, g, hc, hy, _⟩ => ⟨X, x, hc, hy, g.1.z, show 2 ≤ (q.1.k + 7) / 8 by have := g.1.k1; omega,
      show (q.1.k + 7) / 8 < 2 ^ 31 by have := g.1.k2; omega⟩) finish_ct) ?_
  rintro q t ⟨xb, σ, X, x, g, hc, hy, hone⟩
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hR := VG.Proof.Bignum.coprime_pow2 g.1.odd (64 * ((q.1.k + 7) / 8))
  refine WP.mono (pFinish_ok hc g.1.z (by omega) (by omega) hR g.1.n1 hone hy)
    fun t' ⟨hg, _, f, k⟩ => ⟨xb, σ, g.step (f.mono (by simp [finRanges, pdAll, pExpRanges, pBitRanges, bitRanges])) k
      (f.word_eq (fun r hr => by
        have := hdr_lt_slot ((q.1.k + 7) / 8) aAcc (show sMask < 32 by decide)
        have := hdr_lt_slot ((q.1.k + 7) / 8) aTmp (show sMask < 32 by decide)
        have := hdr_lt_slot ((q.1.k + 7) / 8) aY (show sMask < 32 by decide)
        simp only [finRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> omega) (by unfold sMask sFn; omega)), hg⟩

theorem dd_oPre {q : DPub × BitVec 64} {t : State} (h : DD q t) : OPre ⟨DPub.L q, q.1.k, q.1.op⟩ t := by
  obtain ⟨xb, σ, g, hg⟩ := h
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  exact ⟨_, hg, rfl, g.1.z, show 1 ≤ q.1.k by omega, show q.1.k < 2 ^ 31 by omega, by rw [g.fixed sOut (by decide)]; exact g.1.hO,
    by rw [g.fixed sK (by decide)]; exact g.1.hK, g.2.2.2, fun j hj => by rw [g.2.2.1.2.2]; exact g.1.out j hj,
    g.1.outSep⟩

/-- `rest` leaks the same in runs with the same public data and `e`. -/
theorem pdRest_ct : RelCT isa (Two DRel) (Precomputed.rest M.mm) fun _ _ => True := by
  rw [pdRest_eq]
  refine RelCT.seqs_append (by simp [pdIn]) (by simp [pdExp]) (RelCT.seq pdSetup_ct ?_)
  refine RelCT.seqs_append (by simp [pdExp]) (by simp [outSteps]) (RelCT.seq (R := Two DD) ?_ ?_)
  · exact RelCT.seq pdMm_ct (RelCT.seq pdExp_ct pdFinish_ct)
  · exact two_map (fun q => (⟨DPub.L q, q.1.k, q.1.op⟩ : OPub)) (fun _ _ h => dd_oPre h) out_ct

/-! ## The load and the checks -/

/-- The public data of `vg_rsa_public_precomputed`: `rest`'s, `pre` and the
stack pointer. -/
structure CPubD where
  d : DPub
  pp : Addr
  rsp : Addr

/-- What the load keeps. -/
def LH (p : CPubD) (t : State) : Prop :=
  Scr t p.d.B p.d.Z ∧ t.gpr .rdi = p.d.B ∧ slot ((p.d.k + 7) / 8) 8 ≤ p.d.Z ∧ 64 ≤ p.d.k ∧ p.d.k ≤ 1024 ∧
    word t.mem p.d.B (8 * sK) = BitVec.ofNat 64 p.d.k ∧ word t.mem p.d.B (8 * sN) = p.pp ∧
    (∀ i < 2 * ((p.d.k + 7) / 8), InRegions (t.rd ++ t.wr) (off p.pp (8 * i)) 8) ∧
    (∀ j < 16 * ((p.d.k + 7) / 8), p.d.Z ≤ ofs p.d.B (p.pp + BitVec.ofNat 64 j))

theorem LH.congr {p : CPubD} {s t : State} (h : LH p s) {rs : List (Nat × Nat)} (hf : Frm p.d.B rs s.mem t.mem)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : LH p t := by
  obtain ⟨hs, hdi, hZ, hk1, hk2, hK, hN, hpr, hps⟩ := h
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hZ, hk1, hk2, (hfx sK (by decide)).trans hK,
    (hfx sN (by decide)).trans hN, fun i hi => by rw [k.2.1, k.2.2]; exact hpr i hi, hps⟩

theorem pins_LH : Pins LH [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- `LH` with the header's `w` and bases. -/
def LW (p : CPubD) (t : State) : Prop :=
  LH p t ∧ word t.mem p.d.B (8 * sW) = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
    (∀ j < 8, word t.mem p.d.B (8 * sArr j) = off p.d.B (slot ((p.d.k + 7) / 8) j))

/-- A copy of `w` words from `pre + 8 c` into array `j`. -/
theorem ldCopy_ok {p : CPubD} {t : State} (h : LW p t) {c j : Nat} (hc : c ≤ (p.d.k + 7) / 8) (hj : j < 8)
    (hsi : t.gpr .rsi = off p.pp (8 * c)) (hbx : t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) j))
    (h12 : t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) :
    WP isa copyWords t fun t' => LW p t' ∧ Keep [.rax, .r14] t t' := by
  have h₀ : LH p t := h.1
  obtain ⟨⟨hs, hdi, hZ, hk1, hk2, hK, hN, hpr, hps⟩, hW, hb⟩ := h
  have hn := hs.nowrap
  have hsl := slot_le (w := (p.d.k + 7) / 8) hj
  have hge := hdr_lt_slot ((p.d.k + 7) / 8) j (show 31 < 32 by decide)
  have hA : ∀ i < 8, 8 * sArr i + 8 ≤ slot ((p.d.k + 7) / 8) j := fun i hi => by unfold sArr; omega
  refine WP.mono (copyWords_ok (S := p.pp) (eS := 8 * c) hsi hbx h12 (by omega) (by omega) (by omega)
    (fun i hi => by rw [show 8 * c + 8 * i = 8 * (c + i) by omega]; exact hpr _ (by omega))
    (fun i hi => hs.st (by omega))
    (fun i hi b hb => Or.inr (by
      have := hps (8 * c + 8 * i + b) (by omega)
      rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; omega))) fun t' ⟨_, _, ho, k⟩ => ?_
  refine ⟨⟨h₀.congr (Frm.of_outside ho (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; left; omega) k (by decide),
    by rw [ho.word (by unfold sW; omega) (by unfold sW; omega)]; exact hW,
    fun i hi => by rw [ho.word (d := 8 * sArr i) (Or.inl (hA i hi)) (by unfold sArr; omega)]; exact hb i hi⟩, k⟩

/-- The load and the checks leak the same in runs with the same public data. -/
theorem pdLoad_ct : RelCT isa (Two LH) (seqs Precomputed.load) fun _ _ => True := by
  unfold Precomputed.load
  -- `w`, the bases, and the first copy's registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .rsi = off p.pp (8 * 0) ∧
      t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) _
    pins_LH (by taint_decide) ?_) ?_
  · intro p t h
    have h' := h
    obtain ⟨hs, hdi, hZ, hk1, hk2, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    refine WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN) fun t' ⟨h12, _, hsi, hbx, hW, hb, hf, k⟩ =>
      ⟨⟨h.congr hf (fun r hr => ?_) k (by decide), hW, hb⟩, by rw [hsi]; simp [off], hbx, h12⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .rsi = off p.pp (8 * 0) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.rsi, .rbx, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hsi, hbx, h12⟩
    exact WP.mono (ldCopy_ok h (Nat.zero_le _) (by decide) hsi hbx h12) fun t' ⟨h', k⟩ =>
      ⟨h', (k.gpr (by decide)).trans hsi, (k.gpr (by decide)).trans h12⟩
  -- `R² mod m`'s registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .rsi = off p.pp (8 * ((p.d.k + 7) / 8)) ∧
      t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8))
    [.rdi, .rsi, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.1.2.1, h₂.1.1.2.1]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hsi, h12⟩
    have hs := h.1.1
    have hn := hs.nowrap
    have hZ := h.1.2.2.1
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 ((p.d.k + 7) / 8) → r + r + (r + r) + (r + r + (r + r)) =
        BitVec.ofNat 64 (8 * ((p.d.k + 7) / 8)) := by
      rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
    have hsi' : t.gpr .rsi = p.pp := by rw [hsi]; simp [off]
    refine WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t' => t'.gpr .rsi = off p.pp (8 * ((p.d.k + 7) / 8)) ∧
        t'.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧ t'.mem = t.mem) (by
      unfold eightW
      simp only [List.cons_append, List.nil_append]
      xrun [State.ea, hdr, h.1.2.1, hdrOff, hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega),
        h.2.2 aR2 (by decide), h12, hsi', hax8 _ rfl]) rfl)
      fun t' ⟨⟨hsi₁, hbx₁, hm⟩, k⟩ => ⟨⟨h.1.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
        (by decide), by rw [hm]; exact h.2.1, fun j hj => by rw [hm]; exact h.2.2 j hj⟩, hsi₁, hbx₁,
        (k.gpr (by decide)).trans h12⟩
  -- `R² mod m`.
  refine RelCT.seq (two_piece (Ψ := fun p t => LW p t ∧ t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.rsi, .rbx, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hsi, hbx, h12⟩
    exact WP.mono (ldCopy_ok h (Nat.le_refl _) (by decide) hsi hbx h12) fun t' ⟨h', k⟩ =>
      ⟨h', (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h12⟩
  -- The comparison's registers.
  refine RelCT.seq (two_piece (Ψ := fun p t => LH p t ∧ t.gpr .rbx = off p.d.B (slot ((p.d.k + 7) / 8) aR2) ∧
      t.gpr .r10 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧ t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
      t.gpr .rbp = mask false) [.rdi] (fun p s₁ s₂ h₁ h₂ => pins_LH p s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hbx, h12⟩
    have hs := h.1.1
    have hn := hs.nowrap
    have hZ := h.1.2.2.1
    obtain ⟨g0, g8⟩ := slot0_ge ((p.d.k + 7) / 8)
    refine WP.mono (WP.keep [.r10, .rbp] (Q := fun t' => t'.gpr .r10 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧
        t'.gpr .rbp = mask false ∧ t'.mem = t.mem) (by
      xrun [State.ea, hdr, h.1.2.1, hdrOff, hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega),
        h.2.2 aN (by decide)]) rfl)
      fun t' ⟨⟨h10, hbp, hm⟩, k⟩ => ⟨h.1.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
        (by decide), (k.gpr (by decide)).trans hbx, h10, (k.gpr (by decide)).trans h12, hbp⟩
  -- The comparison.
  refine RelCT.seq (two_piece (Ψ := fun (p : CPubD) t => t.gpr .r10 = off p.d.B (slot ((p.d.k + 7) / 8) aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((p.d.k + 7) / 8)) [.rbx, .r10, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]) (by taint_decide) ?_) ?_
  · rintro p t ⟨h, hbx, h10, h12, hbp⟩
    have hZ := h.2.2.1
    have hk1 := h.2.2.2.1
    have hk2 := h.2.2.2.2.1
    exact WP.mono (cmpLoop_ok h.1 hbx h10 h12 hbp (by omega) (by omega)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aR2 < 8 by decide); omega)
      (by have := slot_le (w := (p.d.k + 7) / 8) (show aN < 8 by decide); omega)) fun t' ⟨_, _, k⟩ =>
      ⟨(k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- The checks.
  exact two_taint [.r10, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2, h₂.2]) (by taint_decide)

/-! ## The whole function -/

/-- A state the contract allows, with the public data `p`. -/
def CR (p : CPubD) (s : State) : Prop :=
  pdContract.pre s ∧ s.gpr .rsp = p.rsp ∧ stackArg s 2 = p.d.B ∧ (stackArg s 3).toNat * 8 = p.d.Z ∧
    (s.gpr .rsi).toNat = p.d.k ∧ s.gpr .rdi = p.d.op ∧ s.gpr .rdx = p.pp ∧ s.gpr .r8 = p.d.ep ∧
    stackArg s 0 = p.d.ip ∧ (s.gpr .r9).toNat = p.d.len ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = p.d.eb ∧
    wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8) = p.d.N ∧
    wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8) = p.d.R

/-- What `entry` leaves (`pdEntry_ok`). -/
def PdEnt (s t : State) : Prop :=
  t.gpr .rdi = stackArg s 2 ∧
    word t.mem (stackArg s 2) (8 * 0) = s.gpr .rbx ∧ word t.mem (stackArg s 2) (8 * 1) = s.gpr .rbp ∧
    word t.mem (stackArg s 2) (8 * 2) = s.gpr .r12 ∧ word t.mem (stackArg s 2) (8 * 3) = s.gpr .r13 ∧
    word t.mem (stackArg s 2) (8 * 4) = s.gpr .r14 ∧ word t.mem (stackArg s 2) (8 * 5) = s.gpr .r15 ∧
    word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi ∧ word t.mem (stackArg s 2) (8 * sN) = s.gpr .rdx ∧
    word t.mem (stackArg s 2) (8 * sK) = s.gpr .rsi ∧ word t.mem (stackArg s 2) (8 * sE) = s.gpr .r8 ∧
    word t.mem (stackArg s 2) (8 * sElen) = s.gpr .r9 ∧ word t.mem (stackArg s 2) (8 * sIn) = stackArg s 0 ∧
    Outside (stackArg s 2) 0 (8 * 22) s.mem t.mem ∧ Keep [.r11, .rax, .rdi] s t

theorem pdEntry_split : Precomputed.entry =
    ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++ Precomputed.entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def CE1 (p : CPubD) (t : State) : Prop :=
  ∃ s, CR p s ∧ t.gpr .r11 = p.d.B ∧ t.gpr .rsp = p.rsp ∧ WP isa (.block (Precomputed.entry.drop 1)) t (PdEnt s)

/-- After `entry`. -/
def CE2 (p : CPubD) (t : State) : Prop := ∃ s, CR p s ∧ PdEnt s t

/-- After the load and the checks (`pdLoad_ok`). -/
def CL (p : CPubD) (t : State) : Prop :=
  ∃ s t₁, CR p s ∧ PdEnt s t₁ ∧
    wv t.mem p.d.B (slot ((p.d.k + 7) / 8) aN) ((p.d.k + 7) / 8) = p.d.N ∧
    wv t.mem p.d.B (slot ((p.d.k + 7) / 8) aR2) ((p.d.k + 7) / 8) = p.d.R ∧
    word t.mem p.d.B (8 * sW) = BitVec.ofNat 64 ((p.d.k + 7) / 8) ∧
    (∀ j < 8, word t.mem p.d.B (8 * sArr j) = off p.d.B (slot ((p.d.k + 7) / 8) j)) ∧
    t.zf = some (!(chkv ((p.d.k + 7) / 8) p.d.N p.d.R)) ∧
    Frm p.d.B (pdLoadRanges ((p.d.k + 7) / 8)) t₁.mem t.mem ∧ Keep mmRegs t₁ t

theorem ce2_lh {p : CPubD} {t : State} (h : CE2 p t) : LH p t := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, -, hpp, -⟩, hdi, -, -, -, -, -, -, -, hN, hK, -, -, -, -, k⟩ := h
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  subst hB hZ hk hpp
  exact ⟨c.hs.congr k.2.2, hdi, by dsimp only; unfold slot hdrBytes; omega, c.hk1, c.hk2, by rw [hK, ofNat_toNat64], hN,
    fun i hi => by rw [k.2.1, k.2.2]; exact c.hpr i hi, c.hps⟩

/-- The load's post, from `entry`'s. -/
theorem ce2_load {p : CPubD} {t : State} (h : CE2 p t) : WP isa (seqs Precomputed.load) t (CL p) := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, hs, he⟩ := h
  have hs' := hs
  have he' := he
  obtain ⟨hdi, -, -, -, -, -, -, -, hN, hK, -, -, -, ho₁, k₁⟩ := he'
  obtain ⟨hpre, -, hB, hZ, hk, -, hpp, -, -, -, -, hNv, hRv⟩ := hs
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  have hn := c.hs.nowrap
  have i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem := InScr.of_outside ho₁ (by omega)
  have hz : slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold slot hdrBytes; omega
  refine WP.mono (pdLoad_ok (c.hs.congr k₁.2.2) hdi hz (by omega) (by omega) (by rw [hK, ofNat_toNat64])
    hN (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact c.hpr i hi) c.hps) fun t' ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ => ?_
  rw [pre_wv_entry c i₁ (by omega), hNv] at hN₂
  rw [pre_wv_entry c i₁ (by omega), hRv] at hR₂
  rw [chk_eq (by omega), hN₂, hR₂] at hz₂
  subst hB hZ hk hpp
  exact ⟨s, t, hs', he, hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩

/-- What `fail` needs after the load. -/
theorem cl_fail {p : CPubD} {t : State} (h : CL p t) :
    Scr t p.d.B p.d.Z ∧ t.gpr .rdi = p.d.B ∧ 8 * 32 ≤ p.d.Z ∧ 64 ≤ p.d.k ∧ p.d.k ≤ 1024 ∧
      word t.mem p.d.B (8 * sOut) = p.d.op ∧ word t.mem p.d.B (8 * sK) = BitVec.ofNat 64 p.d.k := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, t₁, ⟨hpre, -, hB, hZ, hk, hop, -⟩, ⟨hdi, -, -, -, -, -, -, hO, -, hK, -, -, -, -, k₁⟩, -, -, -, -, -,
    f, k⟩ := h
  have c := pdCtx_of hpre
  have := c.hZ
  have := c.hk1
  have := c.hk2
  subst hB hZ hk hop
  have x := Fixed.of_frm f (pdLoadRanges_fixed _)
  exact ⟨c.hs.congr (k₁.trans k).2.2, (k.gpr (by decide)).trans hdi, by dsimp only; omega, c.hk1, c.hk2,
    (x sOut (by decide)).trans hO, by rw [x sK (by decide), hK, ofNat_toNat64]⟩

/-- `rest`'s hypotheses after the load, for values that pass the checks. -/
theorem cl_rest {p : CPubD} {t : State} (h : CL p t) (he : isa.eval .e t = some false) : DRel p.d t := by
  obtain ⟨⟨B, Z, k, op, ep, ip, len, eb, N, R⟩, pp, rsp⟩ := p
  obtain ⟨s, t₁, ⟨hpre, -, hB, hZ, hk, hop, hpp, hep, hip, hlen, heb, hNv, hRv⟩,
    ⟨hdi, -, -, -, -, -, -, hO, -, hK, hE, hL, hIn, ho₁, k₁⟩, hN, hR, hW, hb, hz, f, k₂⟩ := h
  have c := pdCtx_of hpre
  have := c.hk1
  subst hB hZ hk hop hpp hep hip hlen heb hNv hRv
  have hchk : chkv (((s.gpr .rsi).toNat + 7) / 8)
      (wv t.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8))
      (wv t.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8)) = true := by
    rw [hN, hR]; simp only [eval, hz, Option.some.injEq] at he; simpa using he
  rw [← chk_eq (by omega)] at hchk
  obtain ⟨hodd, hN1, hRN⟩ := checks_facts (by omega) hchk
  have hp := pdPre_of c hdi hO hK hE hL hIn ho₁ k₁ hW hb f k₂ hodd hN1 hRN
  rw [hN, hR] at hp
  exact ⟨_, hp⟩

/-- `vg_rsa_public_precomputed` leaks the same in runs that agree on the public
data. -/
theorem pdCode_ct : RelCT isa (Two CR) (Precomputed.code M.mm) fun _ _ => True := by
  unfold Precomputed.code
  refine RelCT.seq (R := Two CE2) ?_ ?_
  · rw [pdEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CE1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := pdCtx_of hs.1
    have hZ := c.hZ
    have hk1 := c.hk1
    have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++
        Precomputed.entry.drop 1)) s (PdEnt s) := by
      rw [← pdEntry_split]; exact pdEntry_ok rfl hw c.ha0 c.ha2 c.hsep
    have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
    have hB' : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 2)
      (by xrun [State.ea, e2, c.ha2, hB']) rfl)) fun t ⟨hw', h11, k⟩ =>
        ⟨s, hs, h11.trans hs.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw'⟩
  refine RelCT.seq (R := Two CL) (two_post (pdLoad_ct.mono (fun _ _ h => two_mono (fun _ _ h => ce2_lh h) h)
    fun _ _ h => h) fun p t h => ce2_load h) ?_
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, _, _, z₂, _⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold fail
    refine RelCT.seq (two_piece (Ψ := fun (p : CPubD) t => t.gpr .rsi = p.d.op ∧
        t.gpr .rcx = BitVec.ofNat 64 p.d.k ∧ t.gpr .rdi = p.d.B) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(cl_fail h₁.1).2.1, (cl_fail h₂.1).2.1])
      (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨hs, hdi, hZ, hk1, hk2, hO, hK⟩ := cl_fail h
    have hn := hs.nowrap
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.d.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = p.d.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 p.d.k) (by
      xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hdi⟩
  · -- `rest`.
    exact two_map (fun p => p.d) (fun _ _ h => cl_rest h.1 h.2) pdRest_ct

/-- `wordsAt`'s words determine the numbers they make. -/
theorem wv_of_wordsAt {m m' : Mem} {p : Addr} {n c w : Nat}
    (h : Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt m' p n) (hc : c + w ≤ n) :
    wv m p (8 * c) w = wv m' p (8 * c) w :=
  wv_congr fun i hi => by
    have := congrArg (fun l => l[c + i]?) h
    simp only [Spec.Rsa.wordsAt, List.getElem?_map, List.getElem?_range (show c + i < n by omega),
      Option.map_some, Option.some.injEq] at this
    show m.readW (p + BitVec.ofNat 64 (8 * c + 8 * i)) 64 = m'.readW (p + BitVec.ofNat 64 (8 * c + 8 * i)) 64
    rw [show 8 * c + 8 * i = 8 * (c + i) by omega]
    exact this

/-- The public data of a state. -/
def cpubOfD (s : State) : CPubD :=
  ⟨⟨stackArg s 2, (stackArg s 3).toNat * 8, (s.gpr .rsi).toNat, s.gpr .rdi, s.gpr .r8, stackArg s 0,
    (s.gpr .r9).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat,
    wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8),
    wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8)⟩,
    s.gpr .rdx, s.gpr .rsp⟩

/-- `vg_rsa_public_precomputed` is constant time but for `pre` and `e`. -/
theorem pdCode_constantTime : ConstantTime isa pdContract.pre pdContract.pub (Precomputed.code M.mm) := by
  refine RelCT.constantTime (pdCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cpubOfD s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, -, a2, a3, hw, he⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    have c := pdCtx_of h₂
    have hpl := c.hpl
    rw [r .rcx (by decide), r .rsi (by decide)] at hpl
    rw [r .rdx (by decide), r .rcx (by decide)] at hw
    refine ⟨h₂, r .rsp (by decide), a2.symm, by rw [← a3]; rfl, by rw [r .rsi (by decide)]; rfl, r .rdi (by decide),
      r .rdx (by decide), r .r8 (by decide), a0.symm, by rw [r .r9 (by decide)]; rfl, he.symm, ?_, ?_⟩
    · rw [r .rdx (by decide), r .rsi (by decide), show (0 : Nat) = 8 * 0 from rfl]
      exact (wv_of_wordsAt hw (by omega)).symm
    · rw [r .rdx (by decide), r .rsi (by decide)]
      exact (wv_of_wordsAt hw (by omega)).symm

end VG.Proof.Bignum.X86_64
