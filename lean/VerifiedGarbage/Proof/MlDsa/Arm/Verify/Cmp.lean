import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Hash
import VerifiedGarbage.Proof.MlKem.Arm.CmpSel

/-!
# ML-DSA verification on 32-bit ARM: `c̃′ = c̃`

`cmpAnd` ORs the XORs of the bytes of `c̃′` and `c̃` into `r12` (ML-KEM's
`cmp_step`), and ANDs `r11` with 1 exactly when that is 0 (`cmpAnd_ok`),
without a branch.
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv argOk base_pres ldc_eq)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (Ptr Arg ldc)
open VG.Impl.MlKem.Arm (cmpBody)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## A state that differs but in registers other than the layout's -/

theorem siteCongr {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s)
    (h4 : s'.gpr .r4 = s.gpr .r4) (h5 : s'.gpr .r5 = s.gpr .r5) (h6 : s'.gpr .r6 = s.gpr .r6)
    (h7 : s'.gpr .r7 = s.gpr .r7) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hsp]; exact h.p1, h.s8, by rw [hsp]; exact h.spk,
    by rw [h7]; exact h.r7, by rw [h4]; exact h.r4, by rw [h5]; exact h.r5, by rw [h6]; exact h.r6,
    by rw [hwr]; exact h.cw, by rw [hrd, hwr]; exact h.cr⟩

theorem VC.congr {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s)
    (hr : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VC p STK σ s' :=
  ⟨siteCongr h.site (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)) hsp hrd hwr,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    by rw [hm]; exact h.sav, by rw [hm]; exact h.lr, by rw [hm]; exact h.pk, by rw [hm]; exact h.mu,
    by rw [hm]; exact h.sg⟩

/-! ## The comparison -/

theorem cmpPre_ok {a b : Ptr} (ha : argOk (.ptr a) = true) (hb : argOk (.ptr b) = true) (n : Nat) (s : State) :
    WP isa (.block (Arg.instrs .r0 (.ptr a) ++ Arg.instrs .r1 (.ptr b) ++ ldc .r9 n ++
      ([.mov .r12 (.imm 0)] : List Instr))) s fun s' =>
      s'.gpr .r0 = s.gpr a.1 + BitVec.ofNat 32 a.2 ∧ s'.gpr .r1 = s.gpr b.1 + BitVec.ofNat 32 b.2 ∧
      s'.gpr .r9 = BitVec.ofNat 32 n ∧ s'.gpr .r12 = 0 ∧ (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨na0, -, -, -, -⟩ := pres_ne (base_pres (r := a.1) (by simpa [argOk] using ha)).1
    (base_pres (r := a.1) (by simpa [argOk] using ha)).2
  obtain ⟨nb0, nb1, -, -, -⟩ := pres_ne (base_pres (r := b.1) (by simpa [argOk] using hb)).1
    (base_pres (r := b.1) (by simpa [argOk] using hb)).2
  apply WP.of_runBlock
  simp (config := { decide := true }) only [Arg.instrs, ldc, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some, Option.some.injEq,
    exists_eq_left', gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, na0,
    nb0, nb1, ldc_eq, ↓reduceIte, true_and, and_true]
  intro r hr h9
  have : ¬ r = .r0 ∧ ¬ r = .r1 ∧ ¬ r = .r12 := by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [this, h9, ↓reduceIte]

theorem shr31_eq : ∀ n < 256, (BitVec.ofNat 32 n - 1) >>> 31 = if n = 0 then (1 : BitVec 32) else 0 := by
  decide +kernel

theorem shr31_of {v : BitVec 32} (h : v.toNat < 256) : (v - 1) >>> 31 = if v = 0 then (1 : BitVec 32) else 0 := by
  have := shr31_eq v.toNat h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  rw [this]
  by_cases e : v = 0
  · rw [e]; rfl
  · rw [ite_eq_right (fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))), ite_eq_right e]

theorem cmpPost_ok (s : State) :
    WP isa (.block [.dp .sub .r12 .r12 (.imm 1), .mov .r12 (.shifted .r12 .lsr 31), .dp .and .r11 .r11 (.reg .r12)]) s
      fun s' => s'.gpr .r11 = s.gpr .r11 &&& ((s.gpr .r12 - 1) >>> 31) ∧
        (∀ r ∈ [Reg.r4, .r5, .r6, .r7], s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval,
    Option.map_some, Option.some.injEq, exists_eq_left', gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg,
    ↓reduceIte, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true]

/-- `r11 ← r11 ∧ (the `n` bytes at `a` and `b` are equal)`. -/
theorem cmpAnd_okS {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a b : Ptr} {n : Nat}
    (pa : PtrIn L a n) (pb : PtrIn L b n) (hn : 0 < n) (hn' : n < 2 ^ 32) :
    WP isa (cmpAnd a b n) s fun s' =>
      s'.gpr .r11 = s.gpr .r11 &&& flag (decide (bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n)) ∧
      (∀ r ∈ [Reg.r4, .r5, .r6, .r7], s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  have fS := hs.fitE pa hn
  have fD := hs.fitE pb hn
  have cr : Covers [⟨State.addr (L.ptr (ix a.1) + BitVec.ofNat 32 a.2), n⟩,
      ⟨State.addr (L.ptr (ix b.1) + BitVec.ofNat 32 b.2), n⟩] (s.rd ++ s.wr) := by
    rw [hs.addrE pa hn, hs.addrE pb hn]
    exact Sample.covers_cons (hs.crE pa) (Sample.covers_cons (hs.crE pb) Sample.covers_nil)
  unfold cmpAnd
  refine WP.seq (WP.mono (cmpPre_ok pa.1 pb.1 n s) fun s₁ ⟨g0, g1, g9, g12, cs, m, rd, wr, sp⟩ => ?_)
  rw [hs.base (r := a.1) (by simpa [argOk] using pa.1)] at g0
  rw [hs.base (r := b.1) (by simpa [argOk] using pb.1)] at g1
  refine WP.seq (wp_loop_ne (CmpInv (L.ptr (ix a.1) + BitVec.ofNat 32 a.2) (L.ptr (ix b.1) + BitVec.ofNat 32 b.2)
      n s₁) (N := n) hn (fun k hk s h => cmp_step fS fD hn' (by rw [rd, wr]; exact cr) hk h) (fun s₂ h => ?_)
    ⟨by rw [g0]; simp, by rw [g1]; simp, by rw [g9]; simp, fun _ _ _ => rfl, rfl, rfl, rfl, rfl,
      by rw [g12]; decide, by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩)
  refine WP.mono (cmpPost_ok s₂) fun s' ⟨r11, rs, m', rd', wr', sp'⟩ => ⟨?_, fun r hr => ?_,
    m'.trans (h.mem.trans m), rd'.trans (h.rd.trans rd), wr'.trans (h.wr.trans wr), sp'.trans (h.sp.trans sp)⟩
  · have e11 : s₂.gpr .r11 = s.gpr .r11 :=
      (h.cs .r11 (by decide) (by decide)).trans (cs .r11 (by decide) (by decide))
    rw [r11, shr31_of h.lt, e11]
    congr 1
    have key : s₂.gpr .r12 = 0 ↔ bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n := by
      rw [h.eq, m, ← hs.addrE pa hn, ← hs.addrE pb hn]
      constructor
      · intro he
        exact Proof.MlKem.bytesAt_eq (Proof.MlKem.bytesAt_length _ _ _) fun t ht => by rw [he t ht, Proof.MlKem.bytesAt_getElem]
      · intro he t ht
        have := congrArg (fun L : List Byte => L[t]!) he
        simp only [Proof.MlKem.bytesAt_getElem! _ _ ht] at this
        exact this
    by_cases e : s₂.gpr .r12 = 0
    · simp only [e, decide_eq_true (key.mp e), ↓reduceIte, flag]
    · simp only [e, decide_eq_false (fun h' => e (key.mpr h')), ↓reduceIte, flag, Bool.false_eq_true]
  · rw [rs r hr]
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h9 : r ≠ .r9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    exact (h.cs r hp h9).trans (cs r hp h9)

/-! ## After the comparison -/

/-- At the end of `compute`: `r11` is the samplers' result `R` and whether
`c̃′ = c̃`. -/
abbrev KE (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, VC p STK σ s ∧ hintOf p σ = some h ∧ h.length = p.k ∧ Gd p σ A' cc R ∧
    s.gpr .r11 = R &&& flag (decide (Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen =
      Proof.MlDsa.Verify.vCt p (sgOf p σ)))

theorem cmp_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KF p STK σ s) :
    WP isa (cmpAnd (sc oCT) (.r6, 0) p.ctildeLen) s (KE p STK σ) := by
  obtain ⟨A', cc, hh, R, hk5, hb⟩ := h
  have hk := hF.k
  have hct := hF.ct
  have pa : PtrIn (vlay p STK σ) (sc oCT) p.ctildeLen := by
    refine ⟨rfl, ?_⟩; rcases hct with e | e | e <;> vsep hF [e]
  have pb : PtrIn (vlay p STK σ) (.r6, 0) p.ctildeLen := by
    refine ⟨rfl, ?_⟩; have := hF.sig; have := hF.hint; vsep hF
  refine WP.mono (cmpAnd_okS hk5.vc.site pa pb (by omega) (by omega))
    fun s' ⟨r11, rs, m, rd, wr, sp⟩ => ⟨A', cc, hh, R, hk5.vc.congr rs m sp rd wr, hk5.hh, hk5.hint.1, hk5.gd, ?_⟩
  have e4 : bytesAt s.mem (lpa (vlay p STK σ) (.r6, 0)) p.ctildeLen = Proof.MlDsa.Verify.vCt p (sgOf p σ) := by
    have := sig_slice hk5.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega)
    rw [List.drop_zero] at this
    exact this
  have e0 : bytesAt s.mem (lpa (vlay p STK σ) (sc oCT)) p.ctildeLen = _ := hb
  rw [r11, e0, e4, hk5.r11]

theorem cmp_taint {n : Nat} (hn : n = 32 ∨ n = 48 ∨ n = 64) : ∃ hc, (VG.Arm.taint.check
    (Taint.ofRegs [.r4, .r5, .r6, .r7]) (cmpAnd (sc oCT) (.r6, 0) n) hc).isSome = true := by
  rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem cmp_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KF p STK) (KE p STK) (cmpAnd (sc oCT) (.r6, 0) p.ctildeLen) :=
  ⟨fun _ _ _ h => cmp_ok hF h, rel_of (vtaint4 (cmp_taint hF.ct).choose_spec)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.Arm.Verify
