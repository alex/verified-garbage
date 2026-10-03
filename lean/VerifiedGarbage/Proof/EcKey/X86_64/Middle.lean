import VerifiedGarbage.Proof.EcKey.X86_64.Finish
import VerifiedGarbage.Proof.Ecdsa.X86_64.Middle
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main

/-!
# Elliptic curve public keys on x86-64: `x`, `y`, the checks and the result

`middle` computes `x = X Z^(p-2)` and `y = Y Z^(p-2)` from `X`, `Y` and the
power in `ACC`, each left Montgomery's form by a multiplication by 1
(`pkOps_ok`), then ands the masks of `d ∈ [1, n-1]` and `Z ≠ 0` into the
flag and writes the result (`middle_ok`).
-/

namespace VG.Proof.EcKey.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Impl.EcKey.X86_64 (YM Y)

variable {c : Cfg}

theorem middle_eq (c : Cfg) : Impl.EcKey.X86_64.Cfg.middle c =
    .seq (.block (mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
    (.seq (.block (mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
    (.seq (.block (mul c.MP' (c.sl YM) (c.sl RY) (c.sl ACC)))
    (.seq (.block (mul c.MP' (c.sl Y) (c.sl YM) (c.sl ONE)))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.EcKey.X86_64.Cfg.finish c))))) := rfl

/-- What `middle`'s field operations leave. -/
structure OpsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  wr : s'.wr = s.wr
  unch : Unch base ([XM, X, YM, Y, TMP].map fun i => (c.sl i, 8 * c.n)) s.mem s'.mem
  x_lt : sv c base s' X < c.C.p
  x : (sv c base s' X : ZMod c.C.p) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
  y_lt : sv c base s' Y < c.C.p
  y : (sv c base s' Y : ZMod c.C.p) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)

/-- The four field operations of `middle`. -/
theorem pkOps_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMP : ModOk c.MP' size c.C.p s.mem base) (hacc : sv c base s ACC < c.C.p) (hone : sv c base s ONE = 1)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', OpsPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq (.block (mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
      (.seq (.block (mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
      (.seq (.block (mul c.MP' (c.sl YM) (c.sl RY) (c.sl ACC)))
      (.seq (.block (mul c.MP' (c.sl Y) (c.sl YM) (c.sl ONE))) rest)))) s Q := by
  have h7 := hc.n7
  have hn := hs.nowrap
  have hpR := coprime_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs hMP (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hMP.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₁ i = sv c base s i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₁ hi h₁ h₂
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₁ kP₁ (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide) (by decide), hone]; omega))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have kP₂ := kP₁.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    (sv_keep (MP'_n c) rfl h7 hn k₂ hi h₂ h₃).trans (v₁ hi h₁ h₃)
  have x₂ : (sv c base s₂ X : ZMod c.C.p) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide) (by decide), hone]),
      toM_mul hpR e₁]
  -- `YM = Y · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₂ kP₂ (o := YM) (a := RY) (b := ACC) (by decide)
    (by decide) (by decide) (by rw [v₂ (by decide) (by decide) (by decide) (by decide)]; exact hacc))
    fun s₃ ⟨k₃, _, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have kP₃ := kP₂.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  have v₃ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → i ≠ YM → i ≠ TMP → sv c base s₃ i = sv c base s i :=
    fun hi h₁ h₂ h₃ h₄ => (sv_keep (MP'_n c) rfl h7 hn k₃ hi h₃ h₄).trans (v₂ hi h₁ h₂ h₄)
  -- `Y = YM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₃ kP₃ (o := Y) (a := YM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₃ (by decide) (by decide) (by decide) (by decide) (by decide), hone]; omega))
    fun s₄ ⟨k₄, lt₄, e₄⟩ => h s₄ ?_)
  have X₄ : sv c base s₄ X = sv c base s₂ X := by
    rw [sv_keep (MP'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)]
  have e₃' : sv c base s₃ YM * 2 ^ (64 * c.n) % c.C.p = sv c base s RY * sv c base s ACC % c.C.p := by
    rw [e₃, v₂ (i := RY) (by decide) (by decide) (by decide) (by decide),
      v₂ (i := ACC) (by decide) (by decide) (by decide) (by decide)]
  refine ⟨k₄.scr hs₃, fun r hr => ?_, by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], ?_,
    by rw [X₄]; exact lt₂, by rw [X₄]; exact x₂, lt₄, ?_⟩
  · rw [k₄.gpr r hr, k₃.gpr r hr, k₂.gpr r hr, k₁.gpr r hr]
  · exact (((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp))).trans
      ((unch_slots (MP'_n c) rfl k₃.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₄.unch (l := [XM, X, YM, Y, TMP]) (by simp) (by simp)))).mono
      fun w hw => by
        simp only [List.mem_append, or_self] at hw
        exact hw
  · rw [toM_one_mul hpR (by rw [e₄, v₃ (i := ONE) (by decide) (by decide) (by decide) (by decide) (by decide),
      hone]), toM_mul hpR e₃']

/-- Whether the public key is a point the result encodes: `d` in `[1, n-1]`
and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) : Bool :=
  decide ((0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, `y`, the checks and the result. -/
theorem middle_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hacc : sv c base s ACC < c.C.p)
    (hflag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64) {out : Addr}
    (hr14 : s.gpr .r14 = out) (hw : (⟨out, 1 + 16 * c.n⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 16 * c.n⟩ ⟨base, size⟩) :
    WP isa (Impl.EcKey.X86_64.Cfg.middle c) s fun s' => ∃ xv yv, xv < c.C.p ∧
      (xv : ZMod c.C.p) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      yv < c.C.p ∧ (yv : ZMod c.C.p) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem out (1 + 16 * c.n) =
        (if ok c base s then 4 :: (toBytes (8 * c.n) xv ++ toBytes (8 * c.n) yv)
          else List.replicate (1 + 16 * c.n) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if ok c base s then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hs.nowrap
  have hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [middle_eq]
  refine pkOps_ok hc hs (modP_of hc F.mp) hacc F.one fun s₄ Op => ?_
  have F₄ := F.unch h7 hn (fixedOk_slW (l := [XM, X, YM, Y, TMP]) (by decide)) Op.unch
  have e₄ : ∀ {i}, i < 45 → i ∉ [XM, X, YM, Y, TMP] → sv c base s₄ i = sv c base s i := fun hi hl =>
    sv_unch Op.unch h7 hn hi (apart_slW hl)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (checkRange_ok c Op.scr h0 (sl_le c h7 (i := D) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := Op.scr.of_keepRegs k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have F₆ := (F₄.unch h7 hn fixedOk_flag O₅.unch).unch h7 hn fixedOk_flag O₆.unch
  have e₆ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₆ i = sv c base s₄ i := fun hi hif =>
    (sv_flag O₆ h0 h7 hn hi hif).trans (sv_flag O₅ h0 h7 hn hi hif)
  have hflag₆ : word s₆.mem base (c.sl FLAG) = if ok c base s then BitVec.allOnes 64 else 0 := by
    have hMN : wordsVal s₄.mem base (c.sl MN) c.n = c.C.n := F₄.mn
    have z₄ : wordsVal s₄.mem base (c.sl RZ) c.n = sv c base s RZ := e₄ (by decide) (by decide)
    have d₄ : wordsVal s₄.mem base (c.sl D) c.n = sv c base s D := e₄ (by decide) (by decide)
    rw [f₆, f₅, flag_unch Op.unch h7 h0 hn (by decide), hflag, sv_flag O₅ h0 h7 hn (i := RZ) (by decide)
      (by decide), hMN, z₄, d₄, BitVec.allOnes_and, mask_and]
    simp only [mask, decide_eq_true_eq]
  have hr14₆ : s₆.gpr .r14 = out := by
    rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), Op.gpr _ (r14_not_clob hc.n4), hr14]
  have hw₆ : (⟨out, 1 + 16 * c.n⟩ : Region) ∈ s₆.wr := by rw [k₆.wr, k₅.wr, Op.wr]; exact hw
  refine WP.mono (pkFinish_ok hc hs₆ hr14₆ hw₆ hd F₆.saved _ hflag₆) fun s' ⟨bytes, rax, saved, _⟩ =>
    ⟨_, _, Op.x_lt, Op.x, Op.y_lt, Op.y, ?_, rax, saved⟩
  rw [bytes, e₆ (i := X) (by decide) (by decide), e₆ (i := Y) (by decide) (by decide)]

end VG.Proof.EcKey.X86_64
