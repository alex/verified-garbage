import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Blocks

/-!
# ML-DSA signing on x86-64: what holds of the state between the pieces

The inputs of the function entered in `σ` (`skOf`, `muOf`, `rndOf`); what
holds of every state of it (`St`: `Top`, the layout, and the inputs where they
were), kept by each piece that writes only where `stChk` allows (`St.step`);
and polynomials in slots of the working space (`Pl`), in families of
consecutive slots (`Fam`), kept by pieces that write apart from them
(`Fam.keep`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Parts of buffers -/

theorem inB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} (h : inB bs (r, o) L = true)
    (h2 : o' + l ≤ o + L) : inB bs (r, o') l = true := by
  unfold inB at h ⊢
  split at h
  · rename_i n hn
    simp only [hn, decide_eq_true_eq] at h ⊢
    omega
  · cases h

theorem sepB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} {q : Ptr} {k : Nat}
    (h : sepB bs (r, o) L q k = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : sepB bs (r, o') l q k = true := by
  unfold sepB at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hp, hq⟩, hs⟩ := h
  refine ⟨⟨inB_sub hp h2, hq⟩, ?_⟩
  rcases hs with hs | ⟨he, hs⟩
  · exact .inl hs
  · exact .inr ⟨he, by omega⟩

theorem keepB_sub {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {r : Reg} {o L o' l : Nat} (h : keepB bs ws (r, o) L = true)
    (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : keepB bs ws (r, o') l = true := by
  unfold keepB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨⟨h.1.1, inB_sub h.1.2 h2⟩, fun w hw => sepB_sub (h.2 w hw) h1 h2⟩

/-! ## The inputs -/

section
variable (p : Params)

/-- `sk`, `μ` and `rnd`, in the state `σ` the function is entered in. -/
abbrev skOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) p.skLen
abbrev muOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) 64
abbrev rndOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) 32

end

/-- The three parameter sets. -/
def Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-! ## Every state -/

/-- What holds of every state of the function entered in `σ`. -/
structure St (p : Params) (D : Nat) (σ s : State) : Prop where
  top : Top σ s
  lay : Lay D (sgR p) (sgW p) s
  sk : bytesAt s.mem (pa s (.rbp, 0)) p.skLen = skOf p σ
  mu : bytesAt s.mem (pa s (.r12, 0)) 64 = muOf σ
  rnd : bytesAt s.mem (pa s (.r13, 0)) 32 = rndOf σ

/-- A piece that writes `ws` keeps `St`. -/
def stChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  topChk (sgB p) ws && keepB (sgB p) ws (.rbp, 0) p.skLen && keepB (sgB p) ws (.r12, 0) 64 &&
    keepB (sgB p) ws (.r13, 0) 32

theorem St.step {p : Params} {D : Nat} {σ s s' : State} (h : St p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : stChk p ws = true) : St p D σ s' := by
  simp only [stChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨h.top.step h.lay hP h1, h.lay.post hP (sgB_bases p), (h.lay.keepBytes hP h2).trans h.sk,
    (h.lay.keepBytes hP h3).trans h.mu, (h.lay.keepBytes hP h4).trans h.rnd⟩

/-! ## Polynomials in slots -/

/-- Slot `j` holds `f`. -/
abbrev Pl (s : State) (j : Nat) (f : Poly) : Prop := PolyIs s.mem (pa s (pS j)) f

/-- The `m` slots from `b` hold `f 0, …, f (m - 1)`. -/
def Fam (s : State) (b m : Nat) (f : Nat → Poly) : Prop := ∀ j < m, Pl s (b + j) (f j)

/-- The `m` slots from `b` lie apart from `ws`. -/
def famChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (b m : Nat) : Bool := m == 0 || keepB bs ws (pS b) (1024 * m)

theorem famChk_one {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {b m j : Nat} (h : famChk bs ws b m = true) (hj : j < m) :
    keepB bs ws (pS (b + j)) 1024 = true := by
  simp only [famChk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact absurd hj (Nat.not_lt_zero _)
  · refine keepB_sub h ?_ ?_ <;> simp only [oP] <;> omega

theorem Fam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) {b m : Nat} {f : Nat → Poly}
    (hc : famChk (rbs ++ wbs) ws b m = true) (h : Fam s b m f) : Fam s' b m f :=
  fun j hj => L.keepPoly hP (famChk_one hc hj) (h j hj)

theorem Pl.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) {j : Nat} {f : Poly}
    (hc : keepB (rbs ++ wbs) ws (pS j) 1024 = true) (h : Pl s j f) : Pl s' j f :=
  L.keepPoly hP hc h

theorem Fam.congr {s : State} {b m : Nat} {f g : Nat → Poly} (h : Fam s b m f) (e : ∀ j < m, f j = g j) :
    Fam s b m g := fun j hj => e j hj ▸ h j hj

/-- The first `r` slots of a family, and the rest. -/
theorem Fam.split {s : State} {b m r : Nat} {f : Nat → Poly} (hr : r ≤ m) :
    Fam s b m f ↔ Fam s b r f ∧ Fam s (b + r) (m - r) fun j => f (r + j) := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), fun j hj => by rw [Nat.add_assoc]; exact h (r + j) (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    by_cases e : j < r
    · exact h1 j e
    · have := h2 (j - r) (by omega)
      simp only [show b + r + (j - r) = b + j by omega, show r + (j - r) = j by omega] at this
      exact this

end VG.Proof.MlDsa.X86_64.Sign
