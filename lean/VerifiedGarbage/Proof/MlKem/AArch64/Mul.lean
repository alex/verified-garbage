import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon

/-!
# ML-KEM on AArch64: `vg_mlkem_multiply_ntts`

Untrusted: everything here is checked by Lean. Four pairs of coefficients
per iteration (`multiplyNTTs_even`, `multiplyNTTs_odd`), in the lanes of
vectors (`vpair_ok`), with the `γᵢ` read from the table in `scratch`.
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem

/-- The contract the proof is written against (and verified callers use);
the artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for `vg_mlkem_multiply_ntts(h = x0, f = x1, g = x2,
scratch = x3)`: if the polynomials at `f` and `g` are reduced, writes
`MultiplyNTTs(f, g)` to `h`, reduced. The code may read `f` and `g` (which
may overlap) and read and write `h` and `scratch` (1024 bytes), which
overlap nothing. -/
def mulAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 1024⟩, ⟨s.gpr .x2, 1024⟩] ∧ s.wr = [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x3, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x1, 1024⟩ ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x2, 1024⟩ ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x3, 1024⟩ ∧
    Region.Disjoint ⟨s.gpr .x1, 1024⟩ ⟨s.gpr .x3, 1024⟩ ∧
    Region.Disjoint ⟨s.gpr .x2, 1024⟩ ⟨s.gpr .x3, 1024⟩ ∧
    Reduced s.mem (s.gpr .x1) ∧ Reduced s.mem (s.gpr .x2)
  post s s' :=
    PolyIs s'.mem (s.gpr .x0) (multiplyNTTs (polyAt s.mem (s.gpr .x1)) (polyAt s.mem (s.gpr .x2)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Mul

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

theorem even_val (A B C D Γ : Zq) :
    (A * B + C * D * Γ).val = ((C.val * D.val % q) * Γ.val + A.val * B.val) % q := by
  rw [val_add', val_mul, val_mul, val_mul]
  generalize A.val * B.val = P
  generalize C.val * D.val % q * Γ.val = R
  rw [q_eq]
  omega

theorem odd_val (A B C D : Zq) : (A * D + C * B).val = (A.val * D.val + C.val * B.val) % q := by
  rw [val_add', val_mul, val_mul]
  generalize A.val * D.val = P
  generalize C.val * B.val = R
  rw [q_eq]
  omega

section
variable (s₀ : State)

abbrev hP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x1
abbrev gP : Addr := s₀.gpr .x2
abbrev sP : Addr := s₀.gpr .x3
abbrev F : Poly := polyAt s₀.mem (fP s₀)
abbrev Gp : Poly := polyAt s₀.mem (gP s₀)
/-- Coefficient `j` of the output. -/
def G (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((multiplyNTTs (F s₀) (Gp s₀))[j]!).val
def old (j : Nat) : BitVec 32 := coeffAt s₀.mem (hP s₀) j

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (fP s₀), polyRegion (gP s₀)]
  wr : s₀.wr = [polyRegion (hP s₀), polyRegion (sP s₀)]
  hf : (polyRegion (hP s₀)).Disjoint (polyRegion (fP s₀))
  hg : (polyRegion (hP s₀)).Disjoint (polyRegion (gP s₀))
  hs : (polyRegion (hP s₀)).Disjoint (polyRegion (sP s₀))
  fs : (polyRegion (fP s₀)).Disjoint (polyRegion (sP s₀))
  gs : (polyRegion (gP s₀)).Disjoint (polyRegion (sP s₀))
  f : Reduced s₀.mem (fP s₀)
  g : Reduced s₀.mem (gP s₀)

/-- After `c` times four pairs. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = coeffAddr (hP s₀) (8 * c)
  x1 : s.gpr .x1 = coeffAddr (fP s₀) (8 * c)
  x2 : s.gpr .x2 = coeffAddr (gP s₀) (8 * c)
  x3 : s.gpr .x3 = sP s₀ + BitVec.ofNat 64 (4 * (4 * c))
  x11 : (s.gpr .x11).toNat = 32 - c
  vc : VConsts s
  out : CoeffsUpTo s.mem (hP s₀) (8 * c) (G s₀) (old s₀)
  f : ∀ j < 256, coeffAt s.mem (fP s₀) j = coeffAt s₀.mem (fP s₀) j
  g : ∀ j < 256, coeffAt s.mem (gP s₀) j = coeffAt s₀.mem (gP s₀) j
  tab : ∀ j < 128, s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (gammaTable.getD j 0)

theorem G_even (s₀ : State) {i : Nat} (hi : i < 128) :
    G s₀ (2 * i) = BitVec.ofNat 32 ((((F s₀)[2 * i + 1]!).val * ((Gp s₀)[2 * i + 1]!).val % q *
      gammaTable.getD i 0 + ((F s₀)[2 * i]!).val * ((Gp s₀)[2 * i]!).val) % q) := by
  rw [G, multiplyNTTs_even _ _ hi, even_val, gammaTable_eq, gammas_getD hi]

theorem G_odd (s₀ : State) {i : Nat} (hi : i < 128) :
    G s₀ (2 * i + 1) = BitVec.ofNat 32 ((((F s₀)[2 * i]!).val * ((Gp s₀)[2 * i + 1]!).val +
      ((F s₀)[2 * i + 1]!).val * ((Gp s₀)[2 * i]!).val) % q) := by
  rw [G, multiplyNTTs_odd _ _ hi, odd_val]

/-- `(a + r γ) mod q` depends only on `r mod q`. -/
theorem add_mul_mod {a r r' γ : Nat} (h : r % 3329 = r' % 3329) :
    (a + r * γ) % 3329 = (r' % 3329 * γ + a) % 3329 := by
  rw [Nat.add_comm, Nat.add_mod, Nat.mul_mod, h, Nat.add_mod (r' % 3329 * γ),
    Nat.mul_mod (r' % 3329) γ, Nat.mod_mod]

/-- The arithmetic of four pairs, in the lanes of `v6`, `v7` (`f[2i]`,
`f[2i+1]`), `v19`, `v20` (`g[2i]`, `g[2i+1]`) and `v18` (`γᵢ`). -/
theorem vpair_ok {rest : List Instr} {s : State} {Q : State → Prop} (hc : VConsts s)
    {FE FO GE GO Γ : Nat → Nat} (hFE : Lanes (s.v .v6) FE) (hFO : Lanes (s.v .v7) FO)
    (hGE : Lanes (s.v .v19) GE) (hGO : Lanes (s.v .v20) GO) (hΓ : Lanes (s.v .v18) Γ)
    (b1 : ∀ e < 4, FE e < 3329) (b2 : ∀ e < 4, FO e < 3329) (b3 : ∀ e < 4, GE e < 3329)
    (b4 : ∀ e < 4, GO e < 3329) (b5 : ∀ e < 4, Γ e < 3329)
    (k : ∀ s', VChg [.v21, .v22, .v23, .v24] s s' →
      Lanes (s'.v .v23) (fun e => (FO e * GO e % 3329 * Γ e + FE e * GE e) % 3329) →
      Lanes (s'.v .v24) (fun e => (FE e * GO e + FO e * GE e) % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (([.vop (.mul .v21 .v7 .v20), .vop (.sqdmulh .v22 .v21 .v17), .vop (.mls .v21 .v22 .v16),
      .vop (.mul .v23 .v6 .v19), .vop (.mla .v23 .v21 .v18), .vop (.sqdmulh .v22 .v23 .v17),
      .vop (.mls .v23 .v22 .v16)] : List Instr) ++ vcsub .v23 .v22 ++
      ([.vop (.mul .v24 .v6 .v20), .vop (.mla .v24 .v7 .v19), .vop (.sqdmulh .v22 .v24 .v17),
      .vop (.mls .v24 .v22 .v16)] : List Instr) ++ vcsub .v24 .v22 ++ rest)) s Q := by
  have pp : ∀ {a b : Nat}, a < 3329 → b < 3329 → a * b < 3329 * 3329 := fun ha hb =>
    Nat.mul_lt_mul_of_lt_of_lt ha hb
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `r = f[2i+1] g[2i+1]`, less than `2q`
  refine wp_vop (d := .v21) rfl fun s₁ h₁ => ?_
  have l₁ : Lanes (s₁.v .v21) fun e => FO e * GO e := by
    rw [h₁.v]; exact (lanes_mul hFO hGO).congr fun e he => Nat.mod_eq_of_lt (by
      have := pp (b2 e he) (b4 e he); omega)
  have c₁ := hc.chg h₁.chg
  refine vbar_ok (d := .v21) (t := .v22) (hc := c₁) (hf := l₁)
    (hlt := fun e he => by have := pp (b2 e he) (b4 e he); omega) (k := fun s₂ h₂ l₂ r₂ => ?_)
  have c₂ := c₁.chg h₂
  -- `h[2i] = f[2i] g[2i] + r γᵢ`
  refine wp_vop (d := .v23) rfl fun s₃ h₃ => wp_vop (d := .v23) rfl fun s₄ h₄ => ?_
  have fe₂ : Lanes (s₂.v .v6) FE := by rw [h₂.get .v6, h₁.get .v6]; exact hFE
  have ge₂ : Lanes (s₂.v .v19) GE := by rw [h₂.get .v19, h₁.get .v19]; exact hGE
  have l₃ := lanes_mul fe₂ ge₂
  rw [← h₃.v] at l₃
  have r₃ : Lanes (s₃.v .v21) fun e => FO e * GO e - FO e * GO e * 645083 / 2 ^ 31 * 3329 := by
    rw [h₃.get .v21]; exact l₂
  have γ₃ : Lanes (s₃.v .v18) Γ := by rw [h₃.get .v18, h₂.get .v18, h₁.get .v18]; exact hΓ
  have l₄ := lanes_mla l₃ r₃ γ₃
  rw [← h₄.v] at l₄
  set R := fun e => FO e * GO e - FO e * GO e * 645083 / 2 ^ 31 * 3329 with hR
  have y_lt : ∀ e < 4, FE e * GE e + R e * Γ e < 2 ^ 31 := fun e he => by
    have h1 := pp (b1 e he) (b3 e he)
    have h2 : R e * Γ e ≤ (2 * 3329) * 3329 :=
      Nat.mul_le_mul (Nat.le_of_lt (r₂ e he).1) (Nat.le_of_lt (b5 e he))
    omega
  have l₄' : Lanes (s₄.v .v23) fun e => FE e * GE e + R e * Γ e := l₄.congr fun e he => by
    have h1 := pp (b1 e he) (b3 e he)
    have := y_lt e he
    rw [Nat.mod_eq_of_lt (show FE e * GE e < 2 ^ 32 by omega), Nat.mod_eq_of_lt
      (show R e * Γ e < 2 ^ 32 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have c₄ := c₂.chg (h₃.chg.trans h₄.chg)
  refine vbar_ok (d := .v23) (t := .v22) (hc := c₄) (hf := l₄') (hlt := y_lt)
    (k := fun s₅ h₅ l₅ r₅ => ?_)
  refine vcsub_ok (by decide) (c₄.chg h₅).q l₅ (fun e he => (r₅ e he).1) fun s₆ h₆ l₆ => ?_
  have c₆ := c₄.chg (h₅.trans h₆)
  -- `h[2i+1] = f[2i] g[2i+1] + f[2i+1] g[2i]`
  refine wp_vop (d := .v24) rfl fun s₇ h₇ => wp_vop (d := .v24) rfl fun s₈ h₈ => ?_
  have e₆ : ∀ r, r ∉ [VReg.v21, .v22, .v23] → s₆.v r = s.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h₆.v r (by simp [hr.2.1, hr.2.2]), h₅.v r (by simp [hr.2.1, hr.2.2]), h₄.get r hr.2.2,
      h₃.get r hr.2.2, h₂.v r (by simp [hr.1, hr.2.1]), h₁.get r hr.1]
  have fe₆ : Lanes (s₆.v .v6) FE := by rw [e₆ .v6 (by decide)]; exact hFE
  have go₆ : Lanes (s₆.v .v20) GO := by rw [e₆ .v20 (by decide)]; exact hGO
  have l₇ := lanes_mul fe₆ go₆
  rw [← h₇.v] at l₇
  have fo₇ : Lanes (s₇.v .v7) FO := by rw [h₇.get .v7, e₆ .v7 (by decide)]; exact hFO
  have ge₇ : Lanes (s₇.v .v19) GE := by rw [h₇.get .v19, e₆ .v19 (by decide)]; exact hGE
  have l₈ := lanes_mla l₇ fo₇ ge₇
  rw [← h₈.v] at l₈
  have z_lt : ∀ e < 4, FE e * GO e + FO e * GE e < 2 ^ 31 := fun e he => by
    have := pp (b1 e he) (b4 e he); have := pp (b2 e he) (b3 e he); omega
  have l₈' : Lanes (s₈.v .v24) fun e => FE e * GO e + FO e * GE e := l₈.congr fun e he => by
    have := pp (b1 e he) (b4 e he); have := pp (b2 e he) (b3 e he)
    rw [Nat.mod_eq_of_lt (show FE e * GO e < 2 ^ 32 by omega), Nat.mod_eq_of_lt
      (show FO e * GE e < 2 ^ 32 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have c₈ := c₆.chg (h₇.chg.trans h₈.chg)
  refine vbar_ok (d := .v24) (t := .v22) (hc := c₈) (hf := l₈') (hlt := z_lt)
    (k := fun s₉ h₉ l₉ r₉ => ?_)
  refine vcsub_ok (by decide) (c₈.chg h₉).q l₉ (fun e he => (r₉ e he).1) fun s₁₀ h₁₀ l₁₀ => ?_
  refine k s₁₀ ((((((((h₁.chg.trans h₂).trans h₃.chg).trans h₄.chg).trans h₅).trans h₆).trans
    h₇.chg).trans h₈.chg |>.trans h₉ |>.trans h₁₀).mono) ?_ (l₁₀.congr fun e he => ?_)
  · rw [h₁₀.v .v23 (by decide), h₉.v .v23 (by decide), h₈.get .v23, h₇.get .v23]
    refine l₆.congr fun e he => ?_
    rw [(r₅ e he).2, add_mul_mod (r₂ e he).2]
  · rw [(r₉ e he).2]

theorem step {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < 32) {s : State} (h : Inv s₀ c s) :
    WP isa (.block vmulBody) s fun s' => Inv s₀ (c + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ c + 1 ≠ 32) := by
  show WP isa (.block (.ldrq .v0 .x1 0 :: .ldrq .v1 .x1 16 :: .ldrq .v4 .x2 0 :: .ldrq .v5 .x2 16 ::
    .ldrq .v18 .x3 0 :: .vop (.perm .uzp1 .s4 .v6 .v0 .v1) :: .vop (.perm .uzp2 .s4 .v7 .v0 .v1) ::
    .vop (.perm .uzp1 .s4 .v19 .v4 .v5) :: .vop (.perm .uzp2 .s4 .v20 .v4 .v5) ::
    ([.vop (.mul .v21 .v7 .v20), .vop (.sqdmulh .v22 .v21 .v17), .vop (.mls .v21 .v22 .v16),
      .vop (.mul .v23 .v6 .v19), .vop (.mla .v23 .v21 .v18), .vop (.sqdmulh .v22 .v23 .v17),
      .vop (.mls .v23 .v22 .v16)] ++ vcsub .v23 .v22 ++
      [.vop (.mul .v24 .v6 .v20), .vop (.mla .v24 .v7 .v19), .vop (.sqdmulh .v22 .v24 .v17),
      .vop (.mls .v24 .v22 .v16)] ++ vcsub .v24 .v22 ++
      (.vop (.perm .zip1 .s4 .v0 .v23 .v24) :: .vop (.perm .zip2 .s4 .v1 .v23 .v24) :: .strq .v0 .x0 0 ::
        .strq .v1 .x0 16 :: ([.addImm .x .x0 .x0 32, .addImm .x .x1 .x1 32, .addImm .x .x2 .x2 32,
        .addImm .x .x3 .x3 16, .subImm .x .x11 .x11 1] ++ []))))) s _
  have hj : 8 * c + 4 ≤ 256 := by omega
  have hj' : 8 * c + 4 + 4 ≤ 256 := by omega
  have inF : ∀ {j : Nat}, j + 4 ≤ 256 → InRegions (s.rd ++ s.wr) (coeffAddr (fP s₀) j) 16 :=
    fun hj => by
      rw [h.rd, h.wr, hp.rd, hp.wr]
      exact in_regions (R := polyRegion (fP s₀)) (by simp) (contains_off (by omega) (by decide))
  have inG : ∀ {j : Nat}, j + 4 ≤ 256 → InRegions (s.rd ++ s.wr) (coeffAddr (gP s₀) j) 16 :=
    fun hj => by
      rw [h.rd, h.wr, hp.rd, hp.wr]
      exact in_regions (R := polyRegion (gP s₀)) (by simp) (contains_off (by omega) (by decide))
  -- the loads
  refine wp_ldrq (a := coeffAddr (fP s₀) (8 * c)) (by decide) (by rw [h.x1, ptr_zero]) (inF hj)
    fun s₁ h₁ => ?_
  refine wp_ldrq (a := coeffAddr (fP s₀) (8 * c + 4)) (by decide) (by rw [h₁.gpr, h.x1, coeffAddr_step])
    (by rw [h₁.rd, h₁.wr]; exact inF hj') fun s₂ h₂ => ?_
  refine wp_ldrq (a := coeffAddr (gP s₀) (8 * c)) (by decide) (by rw [h₂.gpr, h₁.gpr, h.x2, ptr_zero])
    (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact inG hj) fun s₃ h₃ => ?_
  refine wp_ldrq (a := coeffAddr (gP s₀) (8 * c + 4)) (by decide)
    (by rw [h₃.gpr, h₂.gpr, h₁.gpr, h.x2, coeffAddr_step])
    (by rw [h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact inG hj') fun s₄ h₄ => ?_
  refine wp_ldrq (a := sP s₀ + BitVec.ofNat 64 (4 * (4 * c))) (by decide)
    (by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, h.x3, ptr_zero])
    (by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr, h.rd, h.wr, hp.rd, hp.wr]
        exact in_rd_wr (in_regions (R := polyRegion (sP s₀)) (by simp)
          (contains_off (by omega) (by decide)))) fun s₅ h₅ => ?_
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have cf : ∀ j < 256, (coeffAt s.mem (fP s₀) j).toNat = ((F s₀)[j]!).val := fun j hj => by
    rw [h.f j hj, polyAt_val hp.f (show j < n by rw [n_eq]; exact hj)]
  have cg : ∀ j < 256, (coeffAt s.mem (gP s₀) j).toNat = ((Gp s₀)[j]!).val := fun j hj => by
    rw [h.g j hj, polyAt_val hp.g (show j < n by rw [n_eq]; exact hj)]
  have lf0 : Lanes (s₅.v .v0) fun e => ((F s₀)[8 * c + e]!).val := by
    rw [h₅.get .v0, h₄.get .v0, h₃.get .v0, h₂.get .v0, h₁.v]
    exact lanes_coeffs fun e he => cf _ (by omega)
  have lf1 : Lanes (s₅.v .v1) fun e => ((F s₀)[8 * c + 4 + e]!).val := by
    rw [h₅.get .v1, h₄.get .v1, h₃.get .v1, h₂.v, h₁.mem]
    exact lanes_coeffs fun e he => cf _ (by omega)
  have lg4 : Lanes (s₅.v .v4) fun e => ((Gp s₀)[8 * c + e]!).val := by
    rw [h₅.get .v4, h₄.get .v4, h₃.v, h₂.mem, h₁.mem]
    exact lanes_coeffs fun e he => cg _ (by omega)
  have lg5 : Lanes (s₅.v .v5) fun e => ((Gp s₀)[8 * c + 4 + e]!).val := by
    rw [h₅.get .v5, h₄.v, h₃.mem, h₂.mem, h₁.mem]
    exact lanes_coeffs fun e he => cg _ (by omega)
  have lγ : Lanes (s₅.v .v18) fun e => gammaTable.getD (4 * c + e) 0 := by
    rw [h₅.v, m₄, read16]
    intro e he
    have t : ∀ j, j < 4 → (s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * (4 * c)) + BitVec.ofNat 64 (4 * j))
        32).toNat = gammaTable.getD (4 * c + j) 0 := fun j hj => by
      rw [ptr_add, show 4 * (4 * c) + 4 * j = 4 * (4 * c + j) by omega, h.tab _ (by omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          have := gammaTable_lt (4 * c + j) (by omega); have hq : q = 3329 := rfl; omega)]
    rw [vword_ofVWords _ _ _ _ he]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl
    · exact t 0 (by decide)
    · exact t 1 (by decide)
    · exact t 2 (by decide)
    · exact t 3 (by decide)
  -- the even and the odd coefficients
  refine wp_vop (d := .v6) rfl fun s₆ h₆ => wp_vop (d := .v7) rfl fun s₇ h₇ =>
    wp_vop (d := .v19) rfl fun s₈ h₈ => wp_vop (d := .v20) rfl fun s₉ h₉ => ?_
  have ev : ∀ {x y : BitVec 128} {A : Nat → Nat}, Lanes x (fun e => A (8 * c + e)) →
      Lanes y (fun e => A (8 * c + 4 + e)) →
      Lanes (VPermOp.eval .uzp1 .s4 x y) (fun e => A (2 * (4 * c + e))) ∧
      Lanes (VPermOp.eval .uzp2 .s4 x y) (fun e => A (2 * (4 * c + e) + 1)) := fun hx hy =>
    ⟨fun e he => by
      show _ = _
      rw [vword_uzp1_s4 _ _ he]
      split
      · rw [hx _ (by omega)]; dsimp only; rw [show 8 * c + 2 * e = 2 * (4 * c + e) by omega]
      · rw [hy _ (by omega)]; dsimp only; rw [show 8 * c + 4 + 2 * (e - 2) = 2 * (4 * c + e) by omega],
     fun e he => by
      show _ = _
      rw [vword_uzp2_s4 _ _ he]
      split
      · rw [hx _ (by omega)]; dsimp only; rw [show 8 * c + (2 * e + 1) = 2 * (4 * c + e) + 1 by omega]
      · rw [hy _ (by omega)]; dsimp only; rw [show 8 * c + 4 + (2 * (e - 2) + 1) = 2 * (4 * c + e) + 1 by omega]⟩
  have fe : Lanes (s₉.v .v6) fun e => ((F s₀)[2 * (4 * c + e)]!).val := by
    rw [h₉.get .v6, h₈.get .v6, h₇.get .v6, h₆.v]; exact (ev (A := fun j => ((F s₀)[j]!).val) lf0 lf1).1
  have fo : Lanes (s₉.v .v7) fun e => ((F s₀)[2 * (4 * c + e) + 1]!).val := by
    rw [h₉.get .v7, h₈.get .v7, h₇.v, h₆.get .v0, h₆.get .v1]; exact (ev (A := fun j => ((F s₀)[j]!).val) lf0 lf1).2
  have ge : Lanes (s₉.v .v19) fun e => ((Gp s₀)[2 * (4 * c + e)]!).val := by
    rw [h₉.get .v19, h₈.v, h₇.get .v4, h₇.get .v5, h₆.get .v4, h₆.get .v5]; exact (ev (A := fun j => ((Gp s₀)[j]!).val) lg4 lg5).1
  have go : Lanes (s₉.v .v20) fun e => ((Gp s₀)[2 * (4 * c + e) + 1]!).val := by
    rw [h₉.v, h₈.get .v4, h₈.get .v5, h₇.get .v4, h₇.get .v5, h₆.get .v4, h₆.get .v5]
    exact (ev (A := fun j => ((Gp s₀)[j]!).val) lg4 lg5).2
  have gγ : Lanes (s₉.v .v18) fun e => gammaTable.getD (4 * c + e) 0 := by
    rw [h₉.get .v18, h₈.get .v18, h₇.get .v18, h₆.get .v18]; exact lγ
  have vc₉ : VConsts s₉ := h.vc.chg (((((((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans
    h₅.chg).trans h₆.chg).trans h₇.chg).trans h₈.chg).trans h₉.chg))
  refine vpair_ok vc₉ fe fo ge go gγ (fun _ _ => val_lt _) (fun _ _ => val_lt _) (fun _ _ => val_lt _)
    (fun _ _ => val_lt _) (fun e he => by have := gammaTable_lt (4 * c + e) (by omega); exact this)
    fun s₁₀ h₁₀ l23 l24 => ?_
  refine wp_vop (d := .v0) rfl fun s₁₁ h₁₁ => wp_vop (d := .v1) rfl fun s₁₂ h₁₂ => ?_
  have g₁₂ : s₁₂.gpr = s.gpr := by
    rw [h₁₂.gpr, h₁₁.gpr, h₁₀.gpr, h₉.gpr, h₈.gpr, h₇.gpr, h₆.gpr, h₅.gpr, h₄.gpr, h₃.gpr, h₂.gpr,
      h₁.gpr]
  have w₁₂ : s₁₂.wr = s₀.wr := by
    rw [h₁₂.wr, h₁₁.wr, h₁₀.wr, h₉.wr, h₈.wr, h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, h.wr]
  have inH : ∀ {j : Nat}, j + 4 ≤ 256 → InRegions s₀.wr (coeffAddr (hP s₀) j) 16 := fun hj => by
    rw [hp.wr]
    exact in_regions (R := polyRegion (hP s₀)) (by simp) (contains_off (by omega) (by decide))
  refine wp_strq (a := coeffAddr (hP s₀) (8 * c)) (by decide) (by rw [g₁₂, h.x0, ptr_zero])
    (by rw [w₁₂]; exact inH hj) fun s₁₃ h₁₃ => ?_
  refine wp_strq (a := coeffAddr (hP s₀) (8 * c + 4)) (by decide)
    (by rw [h₁₃.gpr, g₁₂, h.x0, coeffAddr_step]) (by rw [h₁₃.wr, w₁₂]; exact inH hj') fun s₁₄ h₁₄ => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x0, .x1, .x2, .x3, .x11] s₁₄ w' ∧ w'.mem = s₁₄.mem ∧
      w'.gpr .x0 = s₁₄.gpr .x0 + BitVec.ofNat 64 32 ∧ w'.gpr .x1 = s₁₄.gpr .x1 + BitVec.ofNat 64 32 ∧
      w'.gpr .x2 = s₁₄.gpr .x2 + BitVec.ofNat 64 32 ∧ w'.gpr .x3 = s₁₄.gpr .x3 + BitVec.ofNat 64 16 ∧
      w'.gpr .x11 = s₁₄.gpr .x11 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun u₁ k₁ e₁ => wp_addImm (by decide) fun u₂ k₂ e₂ =>
      wp_addImm (by decide) fun u₃ k₃ e₃ => wp_addImm (by decide) fun u₄ k₄ e₄ =>
      wp_subImm (by decide) fun u₅ k₅ e₅ => wp_nil ⟨((((k₁.keep.trans k₂.keep).trans k₃.keep).trans
        k₄.keep).trans k₅.keep).mono, by rw [k₅.mem, k₄.mem, k₃.mem, k₂.mem, k₁.mem],
        by rw [k₅.get .x0, k₄.get .x0, k₃.get .x0, k₂.get .x0, e₁],
        by rw [k₅.get .x1, k₄.get .x1, k₃.get .x1, e₂, k₁.get .x1],
        by rw [k₅.get .x2, k₄.get .x2, e₃, k₂.get .x2, k₁.get .x2],
        by rw [k₅.get .x3, e₄, k₃.get .x3, k₂.get .x3, k₁.get .x3],
        by rw [e₅, k₄.get .x11, k₃.get .x11, k₂.get .x11, k₁.get .x11]⟩))
    fun s' ⟨⟨k', m', e0, e1, e2, e3, e11⟩, hv⟩ => ?_
  have g₁₄ : s₁₄.gpr = s.gpr := by rw [h₁₄.gpr, h₁₃.gpr, g₁₂]
  have mem₁₂ : s₁₂.mem = s.mem := by
    rw [h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, m₄]
  have mm : s'.mem = (s.mem.write (coeffAddr (hP s₀) (8 * c)) 16 (s₁₁.v .v0)).write
      (coeffAddr (hP s₀) (8 * c + 4)) 16 (s₁₂.v .v1) := by
    rw [m', h₁₄.mem, h₁₃.v, h₁₃.mem, mem₁₂, h₁₂.get .v0]
  have fr : Frame [polyRegion (hP s₀)] s.mem s'.mem := by
    rw [mm]; exact frame16 (frame16 (Frame.refl _ _) hj _) hj' _
  have k₁₄ : Keep [] s s₁₄ := ⟨fun r _ => by rw [g₁₄], by rw [h₁₄.rd, h₁₃.rd, h₁₂.rd, h₁₁.rd,
    h₁₀.rd, h₉.rd, h₈.rd, h₇.rd, h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [h₁₄.wr, h₁₃.wr, w₁₂, h.wr],
    by rw [h₁₄.sp, h₁₃.sp, h₁₂.sp, h₁₁.sp, h₁₀.sp, h₉.sp, h₈.sp, h₇.sp, h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp,
      h₁.sp]⟩
  have c11 : (s₁₄.gpr .x11).toNat = 32 - c := by rw [g₁₄, h.x11]
  have x11' : (s'.gpr .x11).toNat = 32 - (c + 1) := by
    rw [e11, toNat_sub_n (by rw [c11]; simp; omega), c11]; simp; omega
  have dj : ∀ {R : Region}, (polyRegion (hP s₀)).Disjoint R → ∀ r ∈ [polyRegion (hP s₀)], R.Disjoint r :=
    fun hd r hr => by rw [List.mem_singleton.mp hr]; exact hd.symm
  refine ⟨⟨by rw [k'.rd, k₁₄.rd, h.rd], by rw [k'.wr, k₁₄.wr, h.wr], by rw [k'.sp, k₁₄.sp, h.sp],
    ?_, ?_, ?_, ?_, x11', ?_, ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩, by rw [x11']; omega⟩
  · rw [e0, g₁₄, h.x0, coeffAddr, ptr_add, show 4 * (8 * c) + 32 = 4 * (8 * (c + 1)) by omega]
  · rw [e1, g₁₄, h.x1, coeffAddr, ptr_add, show 4 * (8 * c) + 32 = 4 * (8 * (c + 1)) by omega]
  · rw [e2, g₁₄, h.x2, coeffAddr, ptr_add, show 4 * (8 * c) + 32 = 4 * (8 * (c + 1)) by omega]
  · rw [e3, g₁₄, h.x3, ptr_add, show 4 * (4 * c) + 16 = 4 * (4 * (c + 1)) by omega]
  · refine ⟨by rw [hv, h₁₄.v, h₁₃.v, h₁₂.get .v16, h₁₁.get .v16]; exact (vc₉.chg h₁₀).q,
      by rw [hv, h₁₄.v, h₁₃.v, h₁₂.get .v17, h₁₁.get .v17]; exact (vc₉.chg h₁₀).m⟩
  · -- the eight coefficients stored
    have val : ∀ {x : BitVec 32} {v : Nat}, x.toNat = v → v < q → x = BitVec.ofNat 32 v := fun hx hv =>
      BitVec.eq_of_toNat_eq (by rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
        have hq : q = 3329 := rfl; omega)])
    have lt : ∀ a, a % 3329 < q := fun a => Nat.mod_lt _ (by decide)
    have ge_ : ∀ e, e < 8 → e % 2 = 0 → G s₀ (8 * c + e) = BitVec.ofNat 32 (((((F s₀)[2 * (4 * c + e / 2) + 1]!).val *
        ((Gp s₀)[2 * (4 * c + e / 2) + 1]!).val % 3329) * gammaTable.getD (4 * c + e / 2) 0 +
        ((F s₀)[2 * (4 * c + e / 2)]!).val * ((Gp s₀)[2 * (4 * c + e / 2)]!).val) % 3329) := fun e he h2 => by
      rw [show 8 * c + e = 2 * (4 * c + e / 2) by omega, G_even _ (by omega)]
    have go_ : ∀ e, e < 8 → e % 2 = 1 → G s₀ (8 * c + e) = BitVec.ofNat 32 (((((F s₀)[2 * (4 * c + e / 2)]!).val *
        ((Gp s₀)[2 * (4 * c + e / 2) + 1]!).val + ((F s₀)[2 * (4 * c + e / 2) + 1]!).val *
        ((Gp s₀)[2 * (4 * c + e / 2)]!).val) % 3329)) := fun e he h2 => by
      rw [show 8 * c + e = 2 * (4 * c + e / 2) + 1 by omega, G_odd _ (by omega)]
    rw [mm, show 8 * (c + 1) = 8 * c + 4 + 4 by omega]
    refine CoeffsUpTo.write16 (CoeffsUpTo.write16 h.out hj fun e he => ?_) hj' fun e he => ?_
    · rw [h₁₁.v, vword_zip1_s4' _ _ he]
      split
      · rw [ge_ e (by omega) ‹_›]; exact val (l23 _ (by omega)) (lt _)
      · rw [go_ e (by omega) (by omega)]; exact val (l24 _ (by omega)) (lt _)
    · rw [h₁₂.v, h₁₁.get .v23, h₁₁.get .v24, vword_zip2_s4 _ _ he,
        show 8 * c + 4 + e = 8 * c + (4 + e) by omega]
      split
      · rw [ge_ (4 + e) (by omega) (by omega), show (4 + e) / 2 = 2 + e / 2 by omega]
        exact val (l23 _ (by omega)) (lt _)
      · rw [go_ (4 + e) (by omega) (by omega), show (4 + e) / 2 = 2 + e / 2 by omega]
        exact val (l24 _ (by omega)) (lt _)
  · rw [coeffAt_frame fr (dj hp.hf) hj, h.f j hj]
  · rw [coeffAt_frame fr (dj hp.hg) hj, h.g j hj]
  · rw [fr.readW (r := ⟨sP s₀, 1024⟩) (contains_off (by omega) (by decide)) (dj hp.hs) (by decide),
      h.tab j hj]

theorem correct (s₀ : State) (hs : mulAArch64.pre s₀) :
    ∃ t s', Exec isa multiplyNTTs s₀ t s' ∧ abiPreserved s₀ s' ∧ mulAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
  have hp : Pre s₀ := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  suffices h : WP isa multiplyNTTs s₀ fun s' => s'.sp = s₀.sp ∧ mulAArch64.post s₀ s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (table_ok gammaTable (fun k hk => Nat.lt_trans (gammaTable_lt k hk) (by decide))
    (b := .x3) (by decide) fun k hk => by
      rw [hp.wr]
      exact in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off (by omega) (by decide)))
    fun s₁ h₁ => WP.mono (Ntt.vconsts_ok s₁) fun s₃ ⟨k₃, m₃, vc₃, _⟩ => ?_
  refine WP.mono (WP.keepV (by decide) (wp_movz (d := .x11) (imm := 32) (is := [])
    fun s₄ h₄ e₄ => wp_nil (Q := fun s₄ => Keep [.x11] s₃ s₄ ∧ s₄.mem = s₃.mem ∧ (s₄.gpr .x11).toNat = 32)
      ⟨h₄.keep, h₄.mem, by rw [e₄]; rfl⟩)) fun s₄ ⟨⟨k₄, m₄, e₄⟩, hv₄⟩ => ?_
  have k₄' := (h₁.keep.trans k₃).trans k₄
  have m : s₄.mem = s₁.mem := by rw [m₄, m₃]
  have dj : ∀ {R : Region}, R.Disjoint (polyRegion (sP s₀)) →
      ∀ r ∈ [(⟨s₀.gpr .x3, 512⟩ : Region)], R.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hd.sub_right (Region.sub_prefix (by decide))
  have i₀ : Inv s₀ 0 s₄ := by
    refine ⟨k₄'.rd, k₄'.wr, k₄'.sp, ?_, ?_, ?_, ?_, by rw [e₄], ?_, ?_, fun j hj => ?_, fun j hj => ?_,
      fun j hj => ?_⟩
    · rw [k₄'.get .x0, coeffAddr]; exact (BitVec.add_zero _).symm
    · rw [k₄'.get .x1, coeffAddr]; exact (BitVec.add_zero _).symm
    · rw [k₄'.get .x2, coeffAddr]; exact (BitVec.add_zero _).symm
    · rw [k₄'.get .x3]; exact (BitVec.add_zero _).symm
    · exact ⟨by rw [hv₄]; exact vc₃.q, by rw [hv₄]; exact vc₃.m⟩
    · rw [m, Nat.mul_zero]
      intro j hj
      rw [ite_eq_right (Nat.not_lt_zero j), old, coeffAt_frame h₁.frame (dj hp.hs) hj]
    · rw [m, coeffAt_frame h₁.frame (dj hp.fs) hj]
    · rw [m, coeffAt_frame h₁.frame (dj hp.gs) hj]
    · rw [m]; exact h₁.tab j hj
  refine WP.mono (count_loop (by decide) (Inv s₀) (fun c hc s h => step hp hc h) i₀)
    fun s' h => ⟨h.sp, (show CoeffsUpTo _ _ 256 _ _ from h.out).polyIs fun _ _ => rfl⟩

theorem ct : ConstantTime isa mulAArch64.pre mulAArch64.pub multiplyNTTs :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => agree_of hsp (by simp [h0, h1, h2, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x4000, 1024⟩]

theorem mul_verified :
    Verified AArch64.target multiplyNTTs (Spec.MlKem.mulContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.mulContract, Spec.MlKem.mulSig, mulAArch64, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Mul
