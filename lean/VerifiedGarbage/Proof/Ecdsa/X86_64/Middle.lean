import VerifiedGarbage.Proof.Ecdsa.X86_64.SlotOps

/-!
# ECDSA on x86-64: `x`, `r`, `k R mod n` and the checks of `d`, `k`, `r`

`middle` computes `x = X Z^(p-2)` from `X` and the power in `ACC`, left
Montgomery's form (a multiplication by 1), `r = x mod n` (an addition of
zero modulo `n`, as `x < p < 2n`) and `k R mod n` (a multiplication by
`R² mod n`), then ands the masks of `d, k ∈ [1, n-1]` and `r ≠ 0` into the
flag (`middle_ok`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem middle_eq (c : Cfg) : c.middle = .seq (.block (mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
    (.seq (.block (mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
    (.seq (.block (add c.MN' (c.sl RR) (c.sl X) (c.sl ZERO)))
    (.seq (.block (mul c.MN' (c.sl KM) (c.sl K) (c.sl R2N)))
    (.block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR)))))) := rfl

/-- What `middle`'s field operations leave. -/
structure MidPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base ([XM, X, RR, KM, TMP].map fun i => (c.sl i, 8 * c.n)) s.mem s'.mem
  modP : ModOk c.MP' size c.C.p s'.mem base
  modN : ModOk c.MN' size c.C.n s'.mem base
  x_lt : sv c base s' X < c.C.p
  x : (sv c base s' X : ZMod c.C.p) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
  rr : sv c base s' RR = sv c base s' X % c.C.n
  km_lt : sv c base s' KM < c.C.n
  km : toM c.C.n (2 ^ (64 * c.n)) (sv c base s' KM) = (sv c base s K : ZMod c.C.n)

theorem unch_slots {base : Addr} {m₁ m₂ : Mem} {o : Nat} {l : List Nat} {M : Mod} (hMn : M.n = c.n)
    (hMt : M.tmp = c.sl TMP) (h : Unch base [(c.sl o, 8 * M.n), (M.tmp, 8 * M.n)] m₁ m₂)
    (ho : o ∈ l) (ht : TMP ∈ l) : Unch base (l.map fun i => (c.sl i, 8 * c.n)) m₁ m₂ :=
  h.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, hMn, hMt] at hw
    rcases hw with rfl | rfl
    · exact List.mem_map_of_mem ho
    · exact List.mem_map_of_mem ht

/-- The four field operations of `middle`. -/
theorem midOps_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMP : ModOk c.MP' size c.C.p s.mem base) (hMN : ModOk c.MN' size c.C.n s.mem base)
    (hacc : sv c base s ACC < c.C.p) (hone : sv c base s ONE = 1) (hzero : sv c base s ZERO = 0)
    (hr2 : sv c base s R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s', MidPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq (.block (mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC)))
      (.seq (.block (mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE)))
      (.seq (.block (add c.MN' (c.sl RR) (c.sl X) (c.sl ZERO)))
      (.seq (.block (mul c.MN' (c.sl KM) (c.sl K) (c.sl R2N))) rest)))) s Q := by
  have h7 := hc.n7
  have hn := hs.nowrap
  have hpR := coprime_pow_two hc.p_odd (64 * c.n)
  have hnR := coprime_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hpn := hc.p_lt_2n
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs hMP (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hMP.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have kN₁ := hMN.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have one₁ : sv c base s₁ ONE = 1 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hone
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₁ kP₁ (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by omega)) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have kP₂ := kP₁.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have kN₂ := kN₁.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have zero₂ : sv c base s₂ ZERO = 0 := by
    rw [sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide), hzero]
  have x₂ : (sv c base s₂ X : ZMod c.C.p) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, one₁]), toM_mul hpR e₁]
  -- `RR = X mod n`.
  refine WP.seq (WP.mono (slAdd_ok (MN'_n c) h7 hs₂ kN₂ (o := RR) (a := X) (b := ZERO) (by decide)
    (by decide) (by decide) (by omega)) fun s₃ ⟨k₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have kP₃ := kP₂.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  have kN₃ := kN₂.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  have r2₃ : sv c base s₃ R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide), hr2]
  have K₃ : sv c base s₃ K = sv c base s K := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)]
  -- `KM = K · R² mod n`.
  refine WP.seq (WP.mono (slMul_ok (MN'_n c) h7 hs₃ kN₃ (o := KM) (a := K) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [r2₃]; exact Nat.mod_lt _ (by omega))) fun s₄ ⟨k₄, lt₄, e₄⟩ => h s₄ ?_)
  have X₄ : sv c base s₄ X = sv c base s₂ X := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide),
      sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)]
  refine ⟨k₄.scr hs₃, fun r hr => ?_, by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd],
    by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], ?_,
    kP₃.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide),
    kN₃.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide),
    by rw [X₄]; exact lt₂, by rw [X₄]; exact x₂, ?_, lt₄,
    by rw [toM_r2 hnR (by rw [e₄, r2₃]), K₃]⟩
  · rw [k₄.gpr r hr, k₃.gpr r hr, k₂.gpr r hr, k₁.gpr r hr]
  · have l := [XM, X, RR, KM, TMP]
    exact (((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp))).trans
      ((unch_slots (MN'_n c) rfl k₃.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp)).trans
      (unch_slots (MN'_n c) rfl k₄.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp)))).mono
      fun w hw => by
        simp only [List.mem_append, or_self] at hw
        exact hw
  · rw [sv_keep (MN'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide), e₃, zero₂,
      Nat.add_zero, X₄]

end VG.Proof.Ecdsa.X86_64
