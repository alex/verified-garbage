import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Points

/-!
# ECDSA verification on x86-64: `x` and the result

`tail_ok`: from what `points_ok` leaves, the signature's power gives
`Z^(p-2)`, and `final` computes `x = X Z^(p-2)` out of Montgomery's form,
`x R mod n` and `x R - r R mod n`, ands the masks of `Z ≠ 0` and of that
difference being zero (`x ≡ r` modulo `n`) into the flag, returns its low
bit and restores the callee-saved registers (`vfinish_ok`).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Ecdsa.Verify.X86_64 (RM' XN W)

variable {c : Cfg}

theorem raxFlag_ok {s : State} {base : Addr} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rax (.mem (sc d)), .alu .and .rax (.imm 1)]) s fun s' =>
      s'.gpr .rax = word s.mem base d &&& 1 ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    hs.rdi, ld_sc hs hd, Option.some.injEq, exists_eq_left']
  refine ⟨by rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem vfinish_eq (c : Cfg) : Impl.Ecdsa.Verify.X86_64.Cfg.finish c =
    ([.mov .rax (.mem (sc (c.sl FLAG))), .alu .and .rax (.imm 1)] : List Instr) ++
      Spill.restoreCode .rdi Cfg.saved := rfl

/-- The return value and the callee-saved registers. -/
theorem vfinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.Ecdsa.Verify.X86_64.Cfg.finish c)) s fun s' =>
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) := by
  have hF := sl_le c hc.n7 (i := FLAG) (by decide)
  rw [vfinish_eq, WP.block_append_iff]
  refine WP.mono (raxFlag_ok hs (d := c.sl FLAG) (by have := hc.n0; omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₁ (by decide) (fun p hp => ?_)
    (by rw [hs₁.rdi, k₁.2.1]; exact hsv)) fun s₂ ⟨g₂, r₂, _, _, _⟩ => ⟨?_, g₂⟩
  · have := saved_lt p hp
    rw [hs₁.rdi]
    exact ⟨_, List.mem_append_right _ hs₁.wr, hs₁.contains (by have : size = 8192 := rfl; omega) (by decide)⟩
  · have hra : Reg.rax ∉ Cfg.saved.map Prod.fst := by decide
    rw [r₂ _ hra, e₁, hf, mask_bit]

/-- `[o] = ([a] - [b]) mod m`, on slots. -/
theorem slSub_ok {M : Mod} {m : Nat} (hMn : M.n = c.n) (h7 : c.n < 7) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOk M size m s.mem base) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hA : sv c base s a < m) (hB : sv c base s b < m) :
    WP isa (.block (Impl.Mont.X86_64.sub M (c.sl o) (c.sl a) (c.sl b))) s fun s' =>
      OpKeep M base (c.sl o) s s' ∧ sv c base s' o = (sv c base s a + m - sv c base s b) % m := by
  have := sub_ok hs hM (o := c.sl o) (a := c.sl a) (b := c.sl b) (by rw [hMn]; exact sl_le c h7 ho)
    (by rw [hMn]; exact sl_le c h7 ha) (by rw [hMn]; exact sl_le c h7 hb) (by rw [hMn]; exact hA)
    (by rw [hMn]; exact hB)
  rw [hMn] at this
  exact this

theorem final_eq (c : Cfg) : Impl.Ecdsa.Verify.X86_64.Cfg.final c =
    .seq (.block (Impl.Mont.X86_64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
    (.seq (.block (Impl.Mont.X86_64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
    (.seq (.block (Impl.Mont.X86_64.mul c.MN' (c.sl XN) (c.sl X) (c.sl R2N)))
    (.seq (.block (Impl.Mont.X86_64.sub c.MN' (c.sl W) (c.sl XN) (c.sl RM')))
      (.block (c.checkNonzero (c.sl RZ) ++ (Impl.Ecdh.X86_64.Cfg.checkZero c (c.sl W) ++
        Impl.Ecdsa.Verify.X86_64.Cfg.finish c)))))) := by
  simp only [Impl.Ecdsa.Verify.X86_64.Cfg.final, blocks, List.append_assoc]

/-- `Z^(p-2)`, `x`, the last checks and the result. -/
theorem tail_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State} (hP : Pts c s₀ base g Q₁ Q₂ s) :
    WP isa (.seq (pow c.powP) (Impl.Ecdsa.Verify.X86_64.Cfg.final c)) s fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .rax).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hP.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hn3 := hc.n_ge
  have F := hP.fixed
  have hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  -- `Z^(p-2)`.
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc) hpR hP.scr (modP_of hc F.mp)
    hP.rz_lt F.onep hP.t₁ (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega))
    fun s₁ ⟨K₁, U₁, lt₁, v₁⟩ => ?_)
  rw [powWP_eq] at U₁
  have hs₁ := hP.scr.of_keepRegs K₁ (rdi_not_powClob _)
  have F₁ := F.unch h7 hn (fixedOk_slW (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁ h7 hn hi (apart_slW hl)
  rw [final_eq]
  -- `XM = X · ACC`.
  have hM₁ := modP_of hc F₁.mp
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₁ hM₁ (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) lt₁) fun s₂ ⟨k₂, _, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have M₂ := hM₁.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₂ i = sv c base s₁ i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₂ hi h₁ h₂
  -- `X = XM · 1`.
  have one₂ : sv c base s₂ ONE = 1 := (v₂ (by decide) (by decide) (by decide)).trans F₁.one
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₂ M₂ (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [one₂]; omega)) fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have v₃ : ∀ {i}, i < 45 → i ≠ X → i ≠ TMP → sv c base s₃ i = sv c base s₂ i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₃ hi h₁ h₂
  have x₃ : Fin.ofNat c.C.p (sv c base s₃ X) =
      tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) := by
    have acc₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RZ) ^ (c.C.p - 2) := v₁
    rw [toM_one_mul hpR (by rw [e₃, one₂]), toM_mul hpR e₂, acc₁]
    show toM _ _ (sv c base s₁ RX) * _ = toM _ _ (sv c base s RX) * toM _ _ (sv c base s RZ) ^ _
    rw [e₁ (by decide) (by decide)]
  -- `XN = x R mod n`, `W = XN - r R mod n`.
  have hMN₃ := modN_of hc (show wordsVal s₃.mem base (c.sl MN) c.n = c.C.n from
    (v₃ (by decide) (by decide) (by decide)).trans ((v₂ (by decide) (by decide) (by decide)).trans
      ((e₁ (by decide) (by decide)).trans F.mn)))
  have r2₃ : sv c base s₃ R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n :=
    (v₃ (by decide) (by decide) (by decide)).trans ((v₂ (by decide) (by decide) (by decide)).trans
      ((e₁ (by decide) (by decide)).trans F.r2n))
  refine WP.seq (WP.mono (slMul_ok (MN'_n c) h7 hs₃ hMN₃ (o := XN) (a := X) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [r2₃]; exact Nat.mod_lt _ (by omega))) fun s₄ ⟨k₄, lt₄, e₄⟩ => ?_)
  have hs₄ := k₄.scr hs₃
  have M₄ := hMN₃.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide)
  have v₄ : ∀ {i}, i < 45 → i ≠ XN → i ≠ TMP → sv c base s₄ i = sv c base s₃ i := fun hi h₁ h₂ =>
    sv_keep (MN'_n c) rfl h7 hn k₄ hi h₁ h₂
  have rm₄ : sv c base s₄ RM' = sv c base s RM' := by
    rw [v₄ (by decide) (by decide) (by decide), v₃ (by decide) (by decide) (by decide),
      v₂ (by decide) (by decide) (by decide), e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (slSub_ok (MN'_n c) h7 hs₄ M₄ (o := W) (a := XN) (b := RM') (by decide)
    (by decide) (by decide) lt₄ (by rw [rm₄]; exact hP.rm_lt)) fun s₅ ⟨k₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr hs₄
  have v₅ : ∀ {i}, i < 45 → i ≠ W → i ≠ TMP → sv c base s₅ i = sv c base s₄ i := fun hi h₁ h₂ =>
    sv_keep (MN'_n c) rfl h7 hn k₅ hi h₁ h₂
  have w₅ : sv c base s₅ W = 0 ↔ Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀) := by
    have hlt : sv c base s₅ W < c.C.n := by rw [e₅]; exact Nat.mod_lt _ (by omega)
    rw [← toM_eq_zero_iff hnR hlt, e₅, toM_sub (by rw [rm₄]; have := hP.rm_lt; omega), rm₄, hP.rm,
      toM_r2 hnR (by rw [e₄, r2₃])]
    constructor <;> intro h <;> grind
  -- The checks and the result.
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkZero_ok c hs₆ h0 (sl_le c h7 (i := W) (by decide)) hf) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  have U : Unch base (slW c [ACC, PT, TMP, XM, X, XN, W] ++ [(c.sl FLAG, 8)]) s.mem s₇.mem := by
    refine (U₁.trans ((unch_slots (MP'_n c) rfl k₂.unch (l := [XM, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MP'_n c) rfl k₃.unch (l := [X, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MN'_n c) rfl k₄.unch (l := [XN, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MN'_n c) rfl k₅.unch (l := [W, TMP]) (by simp) (by simp)).trans
      (O₆.unch.trans O₇.unch)))))).mono fun w hw => ?_
    have sl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ [ACC, PT, TMP, XM, X, XN, W]) → w ∈ slW c l →
        w ∈ slW c [ACC, PT, TMP, XM, X, XN, W] ++ [(c.sl FLAG, 8)] := fun hl hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (hl i hi))
    simp only [List.mem_append] at hw
    rcases hw with hw | hw | hw | hw | hw | hw | hw
    · exact sl (by decide) hw
    · exact sl (by decide) hw
    · exact sl (by decide) hw
    · exact sl (by decide) hw
    · exact sl (by decide) hw
    · exact List.mem_append_right _ hw
    · exact List.mem_append_right _ hw
  have hsv : Spill.Saved s₇.mem base g Cfg.saved :=
    Saved.unch F.saved (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        show 48 ≤ c.sl i
        rw [sl_eq]; omega
      · rw [List.mem_singleton.mp hw]
        show 48 ≤ c.sl FLAG
        rw [sl_eq]; omega)
      U
  have z₆ : sv c base s₅ RZ = sv c base s RZ := by
    rw [v₅ (by decide) (by decide) (by decide), v₄ (by decide) (by decide) (by decide),
      v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide) (by decide),
      e₁ (by decide) (by decide)]
  have hflag : word s₇.mem base (c.sl FLAG) = if decide ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
      (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
      Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀)) then BitVec.allOnes 64 else 0 := by
    have hW₆ : wordsVal s₆.mem base (c.sl W) c.n = sv c base s₅ W :=
      sv_flag O₆ h0 h7 hn (by decide) (by decide)
    have U₅ : Unch base (slW c [ACC, PT, TMP, XM, X, XN, W]) s.mem s₅.mem := by
      refine (U₁.trans ((unch_slots (MP'_n c) rfl k₂.unch (l := [XM, TMP]) (by simp) (by simp)).trans
        ((unch_slots (MP'_n c) rfl k₃.unch (l := [X, TMP]) (by simp) (by simp)).trans
        ((unch_slots (MN'_n c) rfl k₄.unch (l := [XN, TMP]) (by simp) (by simp)).trans
        (unch_slots (MN'_n c) rfl k₅.unch (l := [W, TMP]) (by simp) (by simp)))))).mono fun w hw => ?_
      have sl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ [ACC, PT, TMP, XM, X, XN, W]) → w ∈ slW c l →
          w ∈ slW c [ACC, PT, TMP, XM, X, XN, W] := fun hl hw => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_map_of_mem (hl i hi)
      simp only [List.mem_append] at hw
      rcases hw with hw | hw | hw | hw | hw
      · exact sl (by decide) hw
      · exact sl (by decide) hw
      · exact sl (by decide) hw
      · exact sl (by decide) hw
      · exact sl (by decide) hw
    have z₆' : wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s RZ := z₆
    rw [f₇, f₆, hW₆, flag_unch U₅ h7 h0 hn (by decide), hP.flag, z₆', mask_and, mask_and]
    simp only [mask, w₅, decide_eq_true_eq, and_assoc]
  refine WP.mono (vfinish_ok hc hs₇ hsv _ hflag) fun s' ⟨rax, saved⟩ => ⟨saved, _, lt₃, x₃, ?_⟩
  rw [rax]
  simp only [decide_eq_true_eq]

end VG.Proof.Ecdsa.Verify.X86_64
