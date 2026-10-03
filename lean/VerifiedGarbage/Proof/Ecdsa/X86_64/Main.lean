import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Rep
import VerifiedGarbage.Proof.Ecdsa.Sign

/-!
# ECDSA on x86-64: the whole function

`sign_ok`: `Cfg.sign` computes the specification's signature of the hash
with `d` and `k`, for any curve the proof of the code supports (`CfgOk`)
whose group law the proofs support (`Good`), and restores the callee-saved
registers. Four stages, each a lemma: the setup and the tables of bits
(`stage₁`, in `Stages.lean`), `[k]G` and `Z^(p-2)` (`stage₂`), `x`, `r`, the
checks and `k^(n-2)` (`stage₃`), and `s`, its check and the result
(`stage₄`); `signWith_eq` connects what they compute to the specification.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

variable {c : Cfg}

/-- After `[k]G` and `Z^(p-2)`. -/
structure St₂ (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = kv c s₀
  d : sv c base s D = dv c s₀
  e : sv c base s E = ev c s₀
  flag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c s₀) (G c.C))
  acc_lt : sv c base s ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) = tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s RZ < c.C.p

/-- `[k]G`, then `Z^(p-2)`. -/
theorem stage₂ (hc : CfgOk c) (hC : Good c.C) {s₀ : State} {base : Addr} {s : State} (hS : St₁ c s₀ base s)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq (ladder c.ladderCfg) (.seq (pow c.powP) rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hS.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hS.fixed
  have hkl : kv c s₀ < 2 ^ (64 * c.n) := hS.k ▸ wordsVal_lt _ _ _ _
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hlt : ∀ x ∈ ladR c.ladderCfg, wordsVal s.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact F.ap.trans_lt (hmont _)
    · exact F.b3p.trans_lt (hmont _)
    · exact F.gx.trans_lt (hmont _)
    · exact F.gy.trans_lt (hmont _)
    · exact F.onep.trans_lt (Nat.mod_lt _ (by omega))
    · exact hS.rx.trans_lt (by omega)
    · exact hS.ry.trans_lt (hmont _)
    · exact hS.rz.trans_lt (by omega)
  have hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
      (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s.mem base (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem base (c.sl GY) c.n))
      (toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  have hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) (mul (kv c s₀ >>> (64 * c.n)) (G c.C)) := by
    show Rep c.C (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ)) _
    rw [hS.rx, hS.ry, hS.rz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  have hstep := step_rep (L := c.ladderCfg) (k := kv c s₀) hC hc.onG (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl AP) c.n) = _
      rw [F.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl B3P) c.n) = _
      rw [F.b3p]; exact toM_cmont hc _) hG
  refine WP.seq (WP.mono (ladder_ok (ladLay hc) hpR hS.scr (modP_of hc F.mp) hlt hstep hR hS.t₀)
    fun s₅ ⟨K₅, U₅, M₅, L₅, R₅⟩ => ?_)
  rw [Nat.shiftRight_zero] at R₅
  rw [ladW_eq] at U₅
  have hs₅ := hS.scr.of_keepRegs K₅ (rdi_not_powClob _)
  have F₅ := F.unch h7 hn (fixedOk_slW (by decide)) U₅
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc) hpR hs₅ M₅
    (L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) F₅.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 hn (j := 1) (by decide) ht (tbl_apart_slW (by decide) 1 t)]
      exact hS.t₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [powWP_eq] at U₆
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] →
      i ∉ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] →
      sv c base s₆ i = sv c base s i := fun hi h₁ h₂ =>
    (sv_unch U₆ h7 hn hi (apart_slW h₁)).trans (sv_unch U₅ h7 hn hi (apart_slW h₂))
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₆ i = sv c base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_slW h₁)
  refine ⟨⟨hs₅.of_keepRegs K₆ (rdi_not_powClob _), ?_, by rw [K₆.wr, K₅.wr, hS.wr],
    F₅.unch h7 hn (fixedOk_slW (by decide)) U₆⟩,
    by rw [e₆ (by decide) (by decide) (by decide), hS.k],
    by rw [e₆ (by decide) (by decide) (by decide), hS.d],
    by rw [e₆ (by decide) (by decide) (by decide), hS.e],
    by rw [flag_unch U₆ h7 h0 hn (by decide), flag_unch U₅ h7 h0 hn (by decide), hS.flag], ?_, ?_, lt₆, ?_,
    ?_⟩
  · rw [K₆.gpr _ (r14_not_powClob hc.n4), K₅.gpr _ (r14_not_powClob hc.n4), hS.r14]
  · intro t ht
    rw [tbl_unch U₆ h7 hn (j := 2) (by decide) ht (tbl_apart_slW (by decide) 2 t),
      tbl_unch U₅ h7 hn (j := 2) (by decide) ht (tbl_apart_slW (by decide) 2 t)]
    exact hS.t₂ t ht
  · show Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv c base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]
    exact L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

/-- After `x`, `r`, the checks and `k^(n-2)`. -/
structure St₃ (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  d : sv c base s D = dv c s₀
  e : sv c base s E = ev c s₀
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c s₀) (G c.C))
  x_lt : sv c base s X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s X) =
    tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rr : sv c base s RR = sv c base s X % c.C.n
  flag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64 &&&
    mask (0 < dv c s₀ ∧ dv c s₀ < c.C.n) &&& mask (0 < kv c s₀ ∧ kv c s₀ < c.C.n) &&&
    mask (sv c base s X % c.C.n ≠ 0)
  acc : toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) = Fin.ofNat c.C.n (kv c s₀) ^ (c.C.n - 2)

/-- `x`, `r`, `k R mod n` and the checks, then `k^(n-2)`. -/
theorem stage₃ (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hS : St₂ c s₀ base s)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₃ c s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq c.middle (.seq (pow c.powN) rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hS.scr.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  refine WP.seq ?_
  rw [middle_eq]
  refine midOps_ok hc hS.scr (modP_of hc F.mp) (modN_of hc F.mn) hS.acc_lt F.one F.zero F.r2n
    fun s₇ Mp => ?_
  have F₇ := F.unch h7 hn (fixedOk_slW (l := [XM, X, RR, KM, TMP]) (by decide)) Mp.unch
  refine WP.mono (checks_ok hc Mp.scr F₇.mn) fun s₈ ⟨f₈, k₈, O₈⟩ => ?_
  have hs₈ := Mp.scr.of_keepRegs k₈ (by decide)
  have F₈ := F₇.unch h7 hn fixedOk_flag O₈.unch
  have e₈ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₈ i = sv c base s₇ i := fun hi hf =>
    sv_flag O₈ h0 h7 hn hi hf
  have e₇ : ∀ {i}, i < 45 → i ∉ [XM, X, RR, KM, TMP] → sv c base s₇ i = sv c base s i := fun hi hl =>
    sv_unch Mp.unch h7 hn hi (apart_slW hl)
  refine WP.seq (WP.mono (pow_ok (P := c.powN) (e := c.C.n - 2) (powLayN hc) hnR hs₈ (modN_of hc F₈.mn)
    ((e₈ (i := KM) (by decide) (by decide)).trans_lt Mp.km_lt) F₈.onen
    (fun t ht => by
      show s₈.mem (off base (bitsAt c.n 2 + t)) = _
      rw [tbl_unch O₈.unch h7 hn (j := 2) (by decide) ht (tbl_apart_flag h0 2 t),
        tbl_unch Mp.unch h7 hn (j := 2) (by decide) ht (tbl_apart_slW (by decide) 2 t)]
      exact hS.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega)) fun s₉ ⟨K₉, U₉, lt₉, v₉⟩ => h s₉ ?_)
  rw [powWN_eq] at U₉
  have e₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₉ i = sv c base s₈ i := fun hi hl =>
    sv_unch U₉ h7 hn hi (apart_slW hl)
  -- The slots `middle` and the power do not write.
  have a₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → i ≠ FLAG → i ∉ [XM, X, RR, KM, TMP] →
      sv c base s₉ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    ((e₉ hi h₁).trans (e₈ hi h₂)).trans (e₇ hi h₃)
  have x₉ : sv c base s₉ X = sv c base s₇ X :=
    (e₉ (i := X) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  have rr₉ : sv c base s₉ RR = sv c base s₇ RR :=
    (e₉ (i := RR) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  have tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₉ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₉ i) = toM _ _ (sv c base s i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [a₉ (by decide) (by decide) (by decide) (by decide)]
  refine ⟨⟨hs₈.of_keepRegs K₉ (rdi_not_powClob _), ?_, by rw [K₉.wr, k₈.wr, Mp.wr, hS.wr],
    F₈.unch h7 hn (fixedOk_slW (by decide)) U₉⟩,
    by rw [a₉ (i := D) (by decide) (by decide) (by decide) (by decide), hS.d],
    by rw [a₉ (i := E) (by decide) (by decide) (by decide) (by decide), hS.e],
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact hS.rep,
    by rw [x₉]; exact Mp.x_lt,
    by rw [x₉, Mp.x, tR RX (by simp), tR RZ (by simp), hS.acc],
    by rw [rr₉, x₉]; exact Mp.rr, ?_, ?_⟩
  · rw [K₉.gpr _ (r14_not_powClob hc.n4), k₈.gpr _ (by decide), Mp.gpr _ (r14_not_clob hc.n4), hS.r14]
  · rw [flag_unch U₉ h7 h0 hn (by decide), f₈, flag_unch Mp.unch h7 h0 hn (by decide), hS.flag,
      e₇ (i := D) (by decide) (by decide), e₇ (i := K) (by decide) (by decide), hS.d, hS.k, Mp.rr, x₉]
  · refine v₉.trans ?_
    show toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ KM) ^ _ = _
    rw [e₈ (i := KM) (by decide) (by decide), Mp.km, hS.k]
    rfl

/-- The result the contract asks for: the specification's signature of the
hash with `d` and `k`, big-endian, and `1`, or zeros and `0`. -/
def SignPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdsa.signWith c.C (dv c s₀)
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (8 * c.n))) (kv c s₀) with
  | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .rdi) (16 * c.n) = Spec.Ecdsa.encode c.C rs
  | none => (s'.gpr .rax).setWidth 32 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .rdi) (16 * c.n) = List.replicate (16 * c.n) 0

/-- `s`, its check, and the result. -/
theorem stage₄ (hc : CfgOk c) (hC : Good c.C) {s₀ : State} (hp : Pre c s₀) {base : Addr} (hb : base = s₀.gpr .r8)
    {s : State} (hS : St₃ c s₀ base s) :
    WP isa c.scalar s fun s' => (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ SignPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hS.scr.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  rw [scalar_eq]
  refine scalarIn_ok hc hS.scr (modN_of hc F.mn) F.r2n
    fun s₁₀ hs₁₀ hM₁₀ g₁₀ _ wr₁₀ U₁₀ _ dm em trm tdm tem => ?_
  have F₁₀ := F.unch h7 hn (fixedOk_slW (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₀
  refine scalarOut_ok hc hs₁₀ hM₁₀ F₁₀.one dm em
    fun s₁₁ hs₁₁ g₁₁ _ wr₁₁ U₁₁ ss_lt ss => ?_
  have hF := sl_le c h7 (i := FLAG) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₁₁ h0 (sl_le c h7 (i := SS) (by decide)) (by omega))
    fun s₁₂ ⟨f₁₂, k₁₂, O₁₂⟩ => ?_
  have hs₁₂ := hs₁₁.of_keepRegs k₁₂ (by decide)
  have F₁₂ := (F₁₀.unch h7 hn (fixedOk_slW (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₁).unch
    h7 hn fixedOk_flag O₁₂.unch
  have acc₁₀ : sv c base s₁₀ ACC = sv c base s ACC := sv_unch U₁₀ h7 hn (by decide) (apart_slW (by decide))
  have rr₁₂ : sv c base s₁₂ RR = sv c base s RR :=
    ((sv_flag O₁₂ h0 h7 hn (i := RR) (by decide) (by decide)).trans
      (sv_unch U₁₁ h7 hn (by decide) (apart_slW (by decide)))).trans
      (sv_unch U₁₀ h7 hn (by decide) (apart_slW (by decide)))
  have ss₁₂ : sv c base s₁₂ SS = sv c base s₁₁ SS := sv_flag O₁₂ h0 h7 hn (by decide) (by decide)
  -- The flag.
  have hflag : word s₁₂.mem base (c.sl FLAG) =
      if decide ((((0 < dv c s₀ ∧ dv c s₀ < c.C.n) ∧ (0 < kv c s₀ ∧ kv c s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [f₁₂, flag_unch U₁₁ h7 h0 hn (by decide), flag_unch U₁₀ h7 h0 hn (by decide), hS.flag,
      BitVec.allOnes_and, mask_and, mask_and, mask_and]
    simp only [mask, decide_eq_true_eq]
  have hr14 : s₁₂.gpr .r14 = s₀.gpr .rdi := by
    rw [k₁₂.gpr _ (by decide), g₁₁ _ (r14_not_clob hc.n4), g₁₀ _ (r14_not_clob hc.n4), hS.r14]
  have hw : (⟨s₀.gpr .rdi, 16 * c.n⟩ : Region) ∈ s₁₂.wr := by
    rw [k₁₂.wr, wr₁₁, wr₁₀, hS.wr, hp.wr]; simp
  refine WP.mono (finish_ok hc hs₁₂ hr14 hw (hb ▸ hp.out_sc) F₁₂.saved _ hflag)
    fun s' ⟨bytes, rax, saved, _⟩ => ⟨saved, ?_⟩
  -- The specification.
  have hsig := signWith_eq hC (C := c.C) (d := dv c s₀) (e := ev c s₀) (k := kv c s₀) hS.rep hS.x_lt hS.x
    (s := wordsVal s₁₁.mem base (c.sl SS) c.n) ss_lt (by
      rw [ss, trm, tdm, tem, acc₁₀, hS.acc, hS.rr, hS.d, hS.e, add_comm])
  unfold SignPost
  rw [hashToInt_eq hc, hsig]
  rw [ss₁₂, rr₁₂, hS.rr] at bytes
  by_cases hP : 1 ≤ dv c s₀ ∧ dv c s₀ < c.C.n ∧ 1 ≤ kv c s₀ ∧ kv c s₀ < c.C.n ∧
      sv c base s X % c.C.n ≠ 0 ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0
  · have hd : decide ((((0 < dv c s₀ ∧ dv c s₀ < c.C.n) ∧ (0 < kv c s₀ ∧ kv c s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = true := by
      simp only [decide_eq_true_eq]; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
    refine ⟨by rw [rax, hd]; rfl, ?_⟩
    rw [bytes, hd, ite_eq_left_of_eq_true _ _ (eq_true rfl), Spec.Ecdsa.encode, hc.len]
  · have hd : decide ((((0 < dv c s₀ ∧ dv c s₀ < c.C.n) ∧ (0 < kv c s₀ ∧ kv c s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = false := by
      simp only [decide_eq_false_iff_not]; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
    refine ⟨by rw [rax, hd]; rfl, ?_⟩
    rw [bytes, hd]; rfl

theorem sign_eq (c : Cfg) : c.sign = .seq (.block c.setup) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
    (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
    (.seq (ladder c.ladderCfg) (.seq (pow c.powP) (.seq c.middle (.seq (pow c.powN) c.scalar))))))) := rfl

/-- `vg_ecdsa_<curve>_sign` computes the specification's signature and
restores the callee-saved registers. -/
theorem sign_ok (hc : CfgOk c) (hC : Good c.C) {s₀ : State} (hp : Pre c s₀) :
    WP isa c.sign s₀ fun s' => (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ SignPost c s₀ s' := by
  rw [sign_eq]
  exact stage₁ hc (hp.setup hc.n7) fun _ S₁ => stage₂ hc hC S₁ fun _ S₂ => stage₃ hc S₂ fun _ S₃ =>
    stage₄ hc hC hp rfl S₃

end VG.Proof.Ecdsa.X86_64
