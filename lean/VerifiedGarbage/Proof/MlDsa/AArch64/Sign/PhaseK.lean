import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseC

/-!
# ML-DSA signing on AArch64: the checks of an iteration

`c = SampleInBall(c̃)` at `ĉ` (`ball_ok`), and, if it succeeded, `ĉ = NTT(c)`
and each check of the iteration, their results ANDed into `x24`: the norm of
each `z[r]` (`zR_ok`), of each `r₀[i]` (`r0R_ok`) and of each `ct₀[i]`, with
each hint `h[i]` and the number of its 1s summed at `ONES` (`hR_ok`), and that
sum against `ω` (`onesOk_ok`); so `x24` is 1 exactly when the iteration passes
(`checks_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only Keep wp_movz wp_nil)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `c = SampleInBall(c̃)` of the iteration with counter `κ`, within `maxBounds`. -/
abbrev cV (σ : State) (κ : Nat) : IPoly :=
  (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).getD (Vector.replicate n 0)

/-- `z[r]`, `r₀[i]`, `ct₀[i]`, `w[i] - cs₂[i]`, `w[i] - cs₂[i] + ct₀[i]` and `h[i]`. -/
abbrev Zv (σ : State) (κ r : Nat) : Poly := zF p (S1v p σ) (rppOf p σ) κ (cV p σ κ) r
abbrev R0v (σ : State) (κ i : Nat) : Poly := r0F p (Am p σ) (S2v p σ) (rppOf p σ) κ (cV p σ κ) i
abbrev CT0v (σ : State) (κ i : Nat) : Poly := ct0F (T0v p σ) (cV p σ κ) i
abbrev W'v (σ : State) (κ i : Nat) : Poly := w'F p (Am p σ) (S2v p σ) (rppOf p σ) κ (cV p σ κ) i
abbrev W''v (σ : State) (κ i : Nat) : Poly := w''F p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ (cV p σ κ) i
abbrev Hv (σ : State) (κ i : Nat) : Vector Bool n := hF p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ (cV p σ κ) i

/-- Whether the iteration with counter `κ` passes, once `SampleInBall` succeeded. -/
abbrev PassV (σ : State) (κ : Nat) : Prop :=
  passF p (Am p σ) (S1v p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ (cV p σ κ)

end

/-! ## `SampleInBall` -/

/-- After `SampleInBall`: the commitment, and `c` at `ĉ` if it succeeded. -/
structure IB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : ICw p D σ t p.k s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t)
  r01 : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1
  ok : (s.gpr .x0).setWidth 32 = 1 → Pl s 0 (toRq (cV p σ (p.ℓ * t))) ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  bad : (s.gpr .x0).setWidth 32 = 0 → sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none

def bChk (p : Params) : Bool :=
  ballChkS (sgR p) (sgW p) (cLen p) cP && icwChk p [(cP, 1024), (sc oPS, 2048)] p.k &&
    keepB (sgB p) [(cP, 1024), (sc oPS, 2048)] (sc oCT) (cLen p) && decide ((cLen p, p.τ) ∈ ballParams)

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => (sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem ball_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : bChk p = true) {σ : State} {t : Nat}
    {s : State} (h : IC p D σ t s) : WP isa (ballAt P (cLen p) p.τ cP) s (IB p D σ t) := by
  simp only [bChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, hbp⟩ := hc
  refine WP.mono (ballCall_ok hP h.c.l.st.lay hbp c1) fun s' ⟨hP1, _, hred, hout, hmax⟩ => ?_
  rw [h.ct] at hout hmax
  refine ⟨h.c.step hP1 c2, by rw [h.c.l.st.lay.keepBytes hP1 c3, h.ct], ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rcases hout with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  · refine ⟨?_, hmax h1⟩
    show PolyIs _ _ _
    rw [hP1.pa (by decide)]
    exact ⟨hred h1, ball_val hout h1 (hmax h1)⟩
  · rcases hout with ⟨e, _⟩ | ⟨_, hn⟩
    · rw [h0] at e; cases e
    · exact Option.map_eq_none_iff.mp hn

/-! ## Norms, into `x24` -/

theorem normAt_okB {P : Prims} {D : Nat} (hP : PrimsOk P D) {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay D rbs wbs s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : normChk (rbs ++ wbs) f = true)
    (hr : Reduced s.mem (pa s f)) {a : Prop} [Decidable a] (h15 : s.gpr .x24 = bit a) :
    WP isa (normAt P f B) s fun s' => PPostB D s s' [] ∧
      s'.gpr .x24 = bit (a ∧ normRq [polyAt s.mem (pa s f)] < B) := by
  refine WP.seq (WP.mono (normCall_ok hP L hB hc hr) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  refine WP.mono (and24_ok s1) fun s2 ⟨k2, h15'⟩ => ?_
  refine ⟨PPostB.trans hP1 (postB24 k2 _) (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil), ?_⟩
  rw [h15', bit_and (hcs1.trans h15) hq1]

theorem bit_congr {a b : Prop} [Decidable a] [Decidable b] (h : a ↔ b) : bit a = bit b := by
  by_cases ha : a
  · rw [show bit a = 1 from ifp ha _ _, show bit b = 1 from ifp (h.mp ha) _ _]
  · rw [show bit a = 0 from ifn ha _ _, show bit b = 0 from ifn (fun hb => ha (h.mpr hb)) _ _]

theorem bit01 {a : Prop} [Decidable a] : bit a = 0 ∨ bit a = 1 := by
  by_cases ha : a
  · exact .inr (ifp ha _ _)
  · exact .inl (ifn ha _ _)

theorem bit_one {a : Prop} [Decidable a] : bit a = 1 ↔ a := by
  by_cases ha : a
  · exact ⟨fun _ => ha, fun _ => ifp ha _ _⟩
  · exact ⟨fun h => absurd (h.symm.trans (ifn ha 1 0)) (by decide), fun h => absurd h ha⟩

theorem bit_zero {a : Prop} [Decidable a] : bit a = 0 ↔ ¬ a := by
  by_cases ha : a
  · exact ⟨fun h => absurd (h.symm.trans (ifp ha 1 0)) (by decide), fun h => absurd ha h⟩
  · exact ⟨fun _ => ha, fun _ => ifn ha _ _⟩

theorem forall_lt_succ {P : Nat → Prop} {r : Nat} : ((∀ j < r, P j) ∧ P r) ↔ ∀ j < r + 1, P j :=
  ⟨fun ⟨h1, h2⟩ j hj => by
    rcases (by omega : j < r ∨ j = r) with hj | rfl
    exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega), h r (by omega)⟩⟩

theorem Fam.head {s : State} {b m : Nat} {f : Nat → Poly} (h : Fam s b (m + 1) f) : Pl s b (f 0) := h 0 (by omega)

theorem Fam.tail {s : State} {b m : Nat} {f : Nat → Poly} (h : Fam s b (m + 1) f) :
    Fam s (b + 1) m fun j => f (j + 1) := fun j hj => by
  have := h (j + 1) (by omega)
  show Pl s (b + 1 + j) _
  rw [show b + 1 + j = b + (j + 1) by omega]
  exact this

theorem Fam.shift {s : State} {b m r : Nat} {f : Nat → Poly} (h : Fam s (b + r) (m - r) fun j => f (r + j))
    (hr : r < m) : Fam s (b + (r + 1)) (m - (r + 1)) fun j => f (r + 1 + j) := fun j hj => by
  have := h (j + 1) (by omega)
  show Pl s (b + (r + 1) + j) (f (r + 1 + j))
  rw [show b + (r + 1) + j = b + r + (j + 1) by omega, show r + 1 + j = r + (j + 1) by omega]
  exact this

theorem Fam.zero {s : State} {b m : Nat} {f : Nat → Poly} (h : Fam s b m f) :
    Fam s (b + 0) (m - 0) fun j => f (0 + j) := fun j hj => by
  show Pl s (b + 0 + j) (f (0 + j))
  rw [Nat.add_zero, Nat.zero_add]
  exact h j hj

/-! ## The checks' state -/

/-- The checks of iteration `t`, once `SampleInBall` succeeded: `ĉ = NTT(c)`. -/
structure KB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  l : IL p D σ t s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t)
  c : Pl s 0 (chF (cV p σ (p.ℓ * t)))
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome

def kbChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  ilChk p ws && keepB (sgB p) ws (sc oCT) (cLen p) && keepB (sgB p) ws cP 1024

theorem KB.step {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : KB p D σ t s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : kbChk p ws = true) : KB p D σ t s' := by
  simp only [kbChk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP h1, (L.keepBytes hP h2).trans h.ct, L.keepPoly hP h3 h.c, h.some⟩

/-! ## `z` -/

/-- The checks of `z[j]` for `j < r`, with `ONES = 0` (but `x24`). -/
structure IZb (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  b : KB p D σ t s
  z : Fam s (yBase p) r (Zv p σ (p.ℓ * t))
  y : Fam s (yBase p + r) (p.ℓ - r) fun j => Yv p σ (p.ℓ * t) (r + j)
  w : Fam s (wBase p) p.k (Wv p σ (p.ℓ * t))
  ones : s.mem.readW (pa s (sc oONES)) 64 = 0

/-- The checks of `z[j]` for `j < r`, their results in `x24`. -/
def IZ (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop :=
  IZb p D σ t r s ∧ s.gpr .x24 = bit (∀ j < r, normRq [Zv p σ (p.ℓ * t) j] < p.γ₁ - p.β)

def zfam (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  kbChk p ws && famChk (sgB p) ws (yBase p) r && famChk (sgB p) ws (wBase p) p.k && keepB (sgB p) ws (sc oONES) 8

theorem IZb.step {p : Params} {D : Nat} {σ s s' : State} {t r : Nat} (h : IZb p D σ t r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : zfam p ws r = true)
    (hy : famChk (sgB p) ws (yBase p + r) (p.ℓ - r) = true) : IZb p D σ t r s' := by
  simp only [zfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP hy h.y, Fam.keep L hP h3 h.w,
    (L.keepW hP h4).trans h.ones⟩

/-- What `z[r]` needs of the layout. -/
def zChk (p : Params) (r : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t1P, 1024)]
  let w2 : List (Ptr × Nat) := [(t1P, 1024), (sc oPS, 1024)]
  let w3 : List (Ptr × Nat) := [(yP p r, 1024)]
  mulChk (sgR p) (sgW p) t1P cP (s1P p r) && ipChkS (sgR p) (sgW p) t1P && accChk (sgR p) (sgW p) (yP p r) t1P &&
    normChk (sgB p) (yP p r) && zfam p w1 r && zfam p w2 r && zfam p w3 r && zfam p [] (r + 1) &&
    famChk (sgB p) w1 (yBase p + r) (p.ℓ - r) && famChk (sgB p) w2 (yBase p + r) (p.ℓ - r) &&
    famChk (sgB p) w3 (yBase p + (r + 1)) (p.ℓ - (r + 1)) && famChk (sgB p) [] (yBase p + (r + 1)) (p.ℓ - (r + 1)) &&
    famChk (sgB p) w3 (yBase p) r && keepB (sgB p) w1 (s1P p r) 1024 && decide (p.γ₁ - p.β < 2 ^ 32) &&
    decide (r < p.ℓ)

theorem zR_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : zChk p r = true) {s : State} (h : IZ p D σ t r s) : WP isa (zR P p r) s (IZ p D σ t (r + 1)) := by
  simp only [zChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cn⟩, z1⟩, z2⟩, z3⟩, z4⟩, y1⟩, y2⟩, y3⟩, y4⟩, f3⟩, e1⟩, hB⟩, hr⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have hs1 := h.b.l.k.d.s1 r hr
  unfold zR
  refine WP.seq (WP.mono (mulAt_ok hP.mul L cm h.b.c.1 hs1.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, hs1.2] at hq1
  have I1 := h.step hP1 z1 y1
  refine WP.seq (WP.mono (ipAt_ok (t := nttInv) hP.invNtt I1.b.l.st.lay ci
    (by rw [hP1.pa (by decide)]; exact hq1.1)) fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [hP1.pa (by decide), hq1.2] at hq2
  have I2 := I1.step hP2 z2 y2
  have hy2 : Pl s2 (yBase p + r) (Yv p σ (p.ℓ * t) r) := I2.y 0 (by omega)
  refine WP.seq (WP.mono (addAt_ok hP I2.b.l.st.lay ca hy2.1 (by rw [hP2.pa (by decide), hP1.pa (by decide)]; exact hq2.1))
    fun s3 ⟨hP3, hcs3, hq3⟩ => ?_)
  rw [hy2.2, hP2.pa (pS_bases 1), hP1.pa (pS_bases 1), hq2.2] at hq3
  have L2 := I2.b.l.st.lay
  simp only [zfam, Bool.and_eq_true] at z3 z4
  have hz3 : Pl s3 (yBase p + r) (Zv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (pS_bases _)]
    exact hq3
  have J3 : IZb p D σ t (r + 1) s3 := ⟨I2.b.step hP3 z3.1.1.1, Fam.snoc (Fam.keep L2 hP3 f3 I2.z) hz3,
    Fam.keep L2 hP3 y3 (I2.y.shift hr),
    Fam.keep L2 hP3 z3.1.2 I2.w, (L2.keepW hP3 z3.2).trans I2.ones⟩
  have e15 : s3.gpr .x24 = s.gpr .x24 := by
    rw [hcs3, hcs2, hcs1]
  refine WP.mono (normAt_okB hP J3.b.l.st.lay hB cn hz3.1 (e15.trans h15)) fun s4 ⟨hP4, h4⟩ => ?_
  have L3 := J3.b.l.st.lay
  refine ⟨⟨J3.b.step hP4 z4.1.1.1, Fam.keep L3 hP4 z4.1.1.2 J3.z, Fam.keep L3 hP4 y4 J3.y,
    Fam.keep L3 hP4 z4.1.2 J3.w, (L3.keepW hP4 z4.2).trans J3.ones⟩, ?_⟩
  rw [h4, hz3.2]
  exact bit_congr forall_lt_succ

/-! ## `r₀` -/

/-- The checks of `r₀[j]` for `j < i` (`w[j]` is `w[j] - cs₂[j]`), with `z` checked and `ONES = 0`. -/
structure IRb (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  b : KB p D σ t s
  z : Fam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t))
  w' : Fam s (wBase p) i (W'v p σ (p.ℓ * t))
  w : Fam s (wBase p + i) (p.k - i) fun j => Wv p σ (p.ℓ * t) (i + j)
  ones : s.mem.readW (pa s (sc oONES)) 64 = 0

/-- `z` passed. -/
abbrev ZOk (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.ℓ, normRq [Zv p σ κ j] < p.γ₁ - p.β

def IR (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  IRb p D σ t i s ∧
    s.gpr .x24 = bit (ZOk p σ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ (p.ℓ * t) j] < p.γ₂ - p.β)

def rfam (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  kbChk p ws && famChk (sgB p) ws (yBase p) p.ℓ && famChk (sgB p) ws (wBase p) i && keepB (sgB p) ws (sc oONES) 8

theorem IRb.step {p : Params} {D : Nat} {σ s s' : State} {t i : Nat} (h : IRb p D σ t i s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : rfam p ws i = true)
    (hw : famChk (sgB p) ws (wBase p + i) (p.k - i) = true) : IRb p D σ t i s' := by
  simp only [rfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP h3 h.w', Fam.keep L hP hw h.w,
    (L.keepW hP h4).trans h.ones⟩

/-- What `r₀[i]` needs of the layout. -/
def rChk (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t1P, 1024)]
  let w2 : List (Ptr × Nat) := [(t1P, 1024), (sc oPS, 1024)]
  let w3 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w4 : List (Ptr × Nat) := [(t2P, 1024)]
  mulChk (sgR p) (sgW p) t1P cP (s2P p i) && ipChkS (sgR p) (sgW p) t1P && accChk (sgR p) (sgW p) (wP p i) t1P &&
    rwChk (sgR p) (sgW p) (wP p i) 1024 t2P 1024 && normChk (sgB p) t2P && rfam p w1 i && rfam p w2 i &&
    rfam p w3 i && rfam p w4 (i + 1) && rfam p [] (i + 1) &&
    famChk (sgB p) w1 (wBase p + i) (p.k - i) && famChk (sgB p) w2 (wBase p + i) (p.k - i) &&
    famChk (sgB p) w3 (wBase p + (i + 1)) (p.k - (i + 1)) && famChk (sgB p) w4 (wBase p + (i + 1)) (p.k - (i + 1)) &&
    famChk (sgB p) [] (wBase p + (i + 1)) (p.k - (i + 1)) && keepB (sgB p) w4 (wP p i) 1024 &&
    decide (p.γ₂ - p.β < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k)

theorem r0R_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : rChk p i = true) {s : State} (h : IR p D σ t i s) : WP isa (r0R P p i) s (IR p D σ t (i + 1)) := by
  simp only [rChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cl⟩, cn⟩, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, y1⟩, y2⟩, y3⟩, y4⟩, y5⟩, k4⟩, hB⟩,
    hγ⟩, hi⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have hs2 := h.b.l.k.d.s2 i hi
  unfold r0R
  refine WP.seq (WP.mono (mulAt_ok hP.mul L cm h.b.c.1 hs2.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, hs2.2] at hq1
  have I1 := h.step hP1 z1 y1
  refine WP.seq (WP.mono (ipAt_ok (t := nttInv) hP.invNtt I1.b.l.st.lay ci
    (by rw [hP1.pa (by decide)]; exact hq1.1)) fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [hP1.pa (by decide), hq1.2] at hq2
  have I2 := I1.step hP2 z2 y2
  have hw2 : Pl s2 (wBase p + i) (Wv p σ (p.ℓ * t) i) := I2.w 0 (by omega)
  refine WP.seq (WP.mono (subAt_ok hP I2.b.l.st.lay ca hw2.1
    (by rw [hP2.pa (by decide), hP1.pa (by decide)]; exact hq2.1)) fun s3 ⟨hP3, hcs3, hq3⟩ => ?_)
  rw [hw2.2, hP2.pa (pS_bases 1), hP1.pa (pS_bases 1), hq2.2] at hq3
  have L2 := I2.b.l.st.lay
  simp only [rfam, Bool.and_eq_true] at z3 z4 z5
  have hw3 : Pl s3 (wBase p + i) (W'v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _
    rw [hP3.pa (pS_bases _)]
    exact hq3
  have J3 : IRb p D σ t (i + 1) s3 := ⟨I2.b.step hP3 z3.1.1.1, Fam.keep L2 hP3 z3.1.1.2 I2.z,
    Fam.snoc (Fam.keep L2 hP3 z3.1.2 I2.w') hw3, Fam.keep L2 hP3 y3 (I2.w.shift hi), (L2.keepW hP3 z3.2).trans I2.ones⟩
  refine WP.seq (WP.mono (lowBitsAt_ok hP J3.b.l.st.lay hγ cl hw3.1) fun s4 ⟨hP4, hcs4, hq4⟩ => ?_)
  rw [hw3.2] at hq4
  have L3 := J3.b.l.st.lay
  have J4 : IRb p D σ t (i + 1) s4 := ⟨J3.b.step hP4 z4.1.1.1, Fam.keep L3 hP4 z4.1.1.2 J3.z,
    Fam.keep L3 hP4 z4.1.2 J3.w', Fam.keep L3 hP4 y4 J3.w, (L3.keepW hP4 z4.2).trans J3.ones⟩
  have e15 : s4.gpr .x24 = s.gpr .x24 := by
    rw [hcs4, hcs3, hcs2, hcs1]
  refine WP.mono (normAt_okB hP J4.b.l.st.lay hB cn (by rw [hP4.pa (by decide)]; exact hq4.1) (e15.trans h15))
    fun s5 ⟨hP5, h5⟩ => ?_
  have L4 := J4.b.l.st.lay
  refine ⟨⟨J4.b.step hP5 z5.1.1.1, Fam.keep L4 hP5 z5.1.1.2 J4.z, Fam.keep L4 hP5 z5.1.2 J4.w',
    Fam.keep L4 hP5 y5 J4.w, (L4.keepW hP5 z5.2).trans J4.ones⟩, ?_⟩
  rw [h5, hP4.pa (by decide), hq4.2]
  exact bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
    fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩

/-! ## Hints and their 1s -/

theorem zq_sub_add (a b : Zq) : a - (a + b) = -b := by
  apply Fin.ext
  have ha := a.isLt; have hb := b.isLt
  simp only [Fin.sub_def, Fin.add_def, Fin.neg_def, q] at *
  omega

theorem sub_add_neg (a b : Poly) : sub a (add a b) = neg b := by
  apply Vector.ext
  intro j hj
  simp only [sub, add, neg, Vector.getElem_zipWith, Vector.getElem_map, zq_sub_add]

theorem hintIs_congr {m m' : Mem} {a : Addr} {h : List (Vector Bool n)}
    (hb : ∀ k < 1024, m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k)) (H : HintIs m a 1 h) :
    HintIs m' a 1 h :=
  ⟨H.1, fun i hi j hj => by
    have hn : n = 256 := rfl
    rw [coeffAt_congr₂ hb (show 256 * i + j < 256 by omega)]; exact H.2 i hi j hj⟩

/-- The hints of the first `m` slots from `b`. -/
def HFam (s : State) (b m : Nat) (f : Nat → Vector Bool n) : Prop :=
  ∀ j < m, HintIs s.mem (pa s (pS (b + j))) 1 [f j]

theorem HFam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) {b m : Nat} {f : Nat → Vector Bool n}
    (hc : famChk (rbs ++ wbs) ws b m = true) (h : HFam s b m f) : HFam s' b m f := fun j hj => by
  have hk := famChk_one hc hj
  rw [hP.pa (keepB_bs hk)]
  exact hintIs_congr (VG.Proof.MlKem.bytes_frame hP.frame (L.fdisj hk) (by decide)) (h j hj)

theorem HFam.snoc {s : State} {b m : Nat} {f : Nat → Vector Bool n} (h : HFam s b m f)
    (h' : HintIs s.mem (pa s (pS (b + m))) 1 [f m]) : HFam s b (m + 1) f := fun j hj => by
  rcases (by omega : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- The sum of the 1s of the first `i` hints. -/
abbrev onesSum (f : Nat → Vector Bool n) (i : Nat) : Nat := ((List.range i).map fun j => hintOnes [f j]).sum

theorem onesSum_le (f : Nat → Vector Bool n) : ∀ i, onesSum f i ≤ 256 * i
  | 0 => by simp [onesSum]
  | i + 1 => by
    simp only [onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    have := onesSum_le f i; have := hintOnes_le (f i)
    simp only [onesSum] at *
    omega

theorem onesSum_succ (f : Nat → Vector Bool n) (i : Nat) : onesSum f (i + 1) = onesSum f i + hintOnes [f i] := by
  simp only [onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-! ## `ct₀` and the hint -/

/-- `r₀` passed. -/
abbrev R0Ok (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.k, normRq [R0v p σ κ j] < p.γ₂ - p.β

/-- The checks of `ct₀[j]` for `j < a`, where `w[j]` is `w[j] - cs₂[j] + ct₀[j]`, and the hints `h[j]` for
`j < c`, their 1s summed at `ONES`. -/
structure IHb (p : Params) (D : Nat) (σ : State) (t a c : Nat) (s : State) : Prop where
  b : KB p D σ t s
  z : Fam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t))
  w'' : Fam s (wBase p) a (W''v p σ (p.ℓ * t))
  w' : Fam s (wBase p + a) (p.k - a) fun j => W'v p σ (p.ℓ * t) (a + j)
  h : HFam s 5 c (Hv p σ (p.ℓ * t))
  ones : s.mem.readW (pa s (sc oONES)) 64 = BitVec.ofNat 64 (onesSum (Hv p σ (p.ℓ * t)) c)

def IH (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  IHb p D σ t i i s ∧ s.gpr .x24 = bit ((ZOk p σ (p.ℓ * t) ∧ R0Ok p σ (p.ℓ * t)) ∧
    ∀ j < i, normRq [CT0v p σ (p.ℓ * t) j] < p.γ₂)

def hfam (p : Params) (ws : List (Ptr × Nat)) (a c : Nat) : Bool :=
  kbChk p ws && famChk (sgB p) ws (yBase p) p.ℓ && famChk (sgB p) ws (wBase p) a &&
    famChk (sgB p) ws (wBase p + a) (p.k - a) && famChk (sgB p) ws 5 c

theorem IHb.step {p : Params} {D : Nat} {σ s s' : State} {t a c : Nat} (h : IHb p D σ t a c s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : hfam p ws a c = true)
    (ho : keepB (sgB p) ws (sc oONES) 8 = true) : IHb p D σ t a c s' := by
  simp only [hfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP h3 h.w'', Fam.keep L hP h4 h.w',
    HFam.keep L hP h5 h.h, (L.keepW hP ho).trans h.ones⟩

theorem ones32 {m : Mem} {a : Addr} {x : Nat} (h : m.readW a 64 = BitVec.ofNat 64 x) :
    (m.readW a 64).setWidth 32 = BitVec.ofNat 32 x := by
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- What `h[i]` needs of the layout. -/
def hChk2 (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t3P, 1024)]
  let w2 : List (Ptr × Nat) := [(t3P, 1024), (sc oPS, 1024)]
  let w4 : List (Ptr × Nat) := [(t4P, 1024)]
  let w5 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w7 : List (Ptr × Nat) := [(hP i, 1024)]
  let w8 : List (Ptr × Nat) := [(sc oONES, 8)]
  mulChk (sgR p) (sgW p) t3P cP (t0P p i) && ipChkS (sgR p) (sgW p) t3P && normChk (sgB p) t3P &&
    copyChk (sgB p) (sgW p) t4P (wP p i) 1024 && accChk (sgR p) (sgW p) (wP p i) t3P &&
    accChk (sgR p) (sgW p) t4P (wP p i) && hintChk (sgR p) (sgW p) t4P (wP p i) (hP i) &&
    hfam p w1 i i && hfam p w2 i i && hfam p [] i i && hfam p w4 i i &&
    (kbChk p w5 && famChk (sgB p) w5 (yBase p) p.ℓ && famChk (sgB p) w5 5 i) &&
    hfam p w4 (i + 1) i && hfam p w7 (i + 1) i && hfam p w8 (i + 1) (i + 1) &&
    famChk (sgB p) w5 (wBase p) i && famChk (sgB p) w5 (wBase p + (i + 1)) (p.k - (i + 1)) &&
    keepB (sgB p) w1 (sc oONES) 8 && keepB (sgB p) w2 (sc oONES) 8 && keepB (sgB p) [] (sc oONES) 8 &&
    keepB (sgB p) w4 (sc oONES) 8 && keepB (sgB p) w5 (sc oONES) 8 && keepB (sgB p) w7 (sc oONES) 8 &&
    keepB (sgB p) [] t3P 1024 && keepB (sgB p) w4 t3P 1024 &&
    keepB (sgB p) w5 t4P 1024 && keepB (sgB p) w1 (t0P p i) 1024 &&
    inB (sgB p) (sc oONES) 8 && inB (sgW p) (sc oONES) 8 &&
    decide (p.γ₂ < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k) && decide (256 * p.k < 2 ^ 32)

theorem pa_sc {s s' : State} (h : s'.gpr .x28 = s.gpr .x28) (o : Nat) : pa s' (sc o) = pa s (sc o) := by
  simp only [pa, h]

theorem hR_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : hChk2 p i = true) {s : State} (h : IH p D σ t i s) : WP isa (hR P p i) s (IH p D σ t (i + 1)) := by
  simp only [hChk2, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, cn⟩, cc⟩, ca⟩, cs⟩, ch⟩, g1⟩, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, f5a⟩, f5b⟩, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩, o7⟩, t3⟩, t4⟩, u5⟩, v1⟩, i1⟩, i2⟩, hγ'⟩, hγ⟩, hi⟩, hk⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have ht0 := h.b.l.k.d.t0 i hi
  unfold hR
  -- `ĉ t̂₀[i]`
  refine WP.seq (WP.mono (mulAt_ok hP.mul L cm h.b.c.1 ht0.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, ht0.2] at hq1
  have I1 := h.step hP1 g1 o1
  have b1 : s1.gpr .x28 = s.gpr .x28 := hP1.bs _ (by decide)
  -- `ct₀[i]`
  refine WP.seq (WP.mono (ipAt_ok (t := nttInv) hP.invNtt I1.b.l.st.lay ci (by rw [pa_sc b1]; exact hq1.1))
    fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [pa_sc b1, hq1.2] at hq2
  have I2 := I1.step hP2 g2 o2
  have b2 : s2.gpr .x28 = s.gpr .x28 := (hP2.bs _ (by decide)).trans b1
  have q2 : Pl s2 3 (CT0v p σ (p.ℓ * t) i) := by show PolyIs _ _ _; rw [pa_sc b2]; exact hq2
  -- its norm
  have e2 : s2.gpr .x24 = s.gpr .x24 := by rw [hcs2, hcs1]
  refine WP.seq (WP.mono (normAt_okB hP I2.b.l.st.lay hγ' cn q2.1 (e2.trans h15)) fun s3 ⟨hP3, h3⟩ => ?_)
  rw [q2.2] at h3
  have I3 := I2.step hP3 g3 o3
  have q3 : Pl s3 3 (CT0v p σ (p.ℓ * t) i) := I2.b.l.st.lay.keepPoly hP3 t3 q2
  -- `T4 ← w[i] - cs₂[i]`
  have hw3 : Pl s3 (wBase p + i) (W'v p σ (p.ℓ * t) i) := I3.w' 0 (by omega)
  refine WP.seq (WP.mono (copy_ok I3.b.l.st.lay cc) fun s4 ⟨hP4, hcs4, hb4⟩ => ?_)
  have I4 := I3.step hP4 g4 o4
  have q4 : Pl s4 3 (CT0v p σ (p.ℓ * t) i) := I3.b.l.st.lay.keepPoly hP4 t4 q3
  have r4 : Pl s4 4 (W'v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _; rw [hP4.pa (pS_bases 4)]; exact polyIs_of_bytes hb4 hw3
  have hw4 : Pl s4 (wBase p + i) (W'v p σ (p.ℓ * t) i) := I4.w' 0 (by omega)
  -- `w[i] ← w[i] - cs₂[i] + ct₀[i]`
  refine WP.seq (WP.mono (addAt_ok hP I4.b.l.st.lay ca hw4.1 q4.1) fun s5 ⟨hP5, hcs5, hq5⟩ => ?_)
  rw [hw4.2, q4.2] at hq5
  have L4 := I4.b.l.st.lay
  have hw5 : Pl s5 (wBase p + i) (W''v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _; rw [hP5.pa (pS_bases _)]; exact hq5
  have J5 : IHb p D σ t (i + 1) i s5 := ⟨I4.b.step hP5 g5.1.1, Fam.keep L4 hP5 g5.1.2 I4.z,
    Fam.snoc (Fam.keep L4 hP5 f5a I4.w'') hw5, Fam.keep L4 hP5 f5b (I4.w'.shift hi), HFam.keep L4 hP5 g5.2 I4.h,
    (L4.keepW hP5 o5).trans I4.ones⟩
  have r5 : Pl s5 4 (W'v p σ (p.ℓ * t) i) := L4.keepPoly hP5 u5 r4
  -- `T4 ← -ct₀[i]`
  refine WP.seq (WP.mono (subAt_ok hP J5.b.l.st.lay cs r5.1 hw5.1) fun s6 ⟨hP6, hcs6, hq6⟩ => ?_)
  rw [r5.2, hw5.2, show W''v p σ (p.ℓ * t) i = add (W'v p σ (p.ℓ * t) i) (CT0v p σ (p.ℓ * t) i) from rfl,
    sub_add_neg] at hq6
  have J6 := J5.step hP6 g6 o4
  have r6 : Pl s6 4 (neg (CT0v p σ (p.ℓ * t) i)) := by show PolyIs _ _ _; rw [hP6.pa (pS_bases 4)]; exact hq6
  have hw6 : Pl s6 (wBase p + i) (W''v p σ (p.ℓ * t) i) := J6.w'' i (by omega)
  -- the hint
  refine WP.seq (WP.mono (hintCall_ok hP J6.b.l.st.lay hγ ch r6.1 hw6.1) fun s7 ⟨hP7, hcs7, hq7, he7⟩ => ?_)
  rw [r6.2, hw6.2] at hq7 he7
  have J7 := J6.step hP7 g7 o7
  have hh7 : HFam s7 5 (i + 1) (Hv p σ (p.ℓ * t)) :=
    HFam.snoc J7.h (by rw [hP7.pa (pS_bases _)]; exact hq7)
  -- `ONES`
  have ho7 : (s7.mem.readW (pa s7 (sc oONES)) 64).setWidth 32 = BitVec.ofNat 32 (onesSum (Hv p σ (p.ℓ * t)) i) := ones32 J7.ones
  have L7 := J7.b.l.st.lay
  refine WP.mono (onesAdd_ok s7 (L7.inR i1) (L7.inW i2)) fun s8 ⟨hm8, k8⟩ => ?_
  have hf : Frame [⟨pa s7 (sc oONES), 8⟩] s7.mem s8.mem := by
    rw [hm8]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hP8 : PostB D s7 s8 _ := postB_of_keep k8 (by decide) hf
  have hcs8 : s8.gpr .x24 = s7.gpr .x24 := k8.get .x24
  have hP8' : PPostB D s7 s8 [(sc oONES, 8)] := hP8
  simp only [hfam, Bool.and_eq_true] at g8
  have hS := onesSum_le (Hv p σ (p.ℓ * t)) i
  have hS1 := hintOnes_le (Hv p σ (p.ℓ * t) i)
  have hik : 256 * (i + 1) ≤ 256 * p.k := Nat.mul_le_mul_left _ hi
  refine ⟨⟨J7.b.step hP8' g8.1.1.1.1, Fam.keep L7 hP8' g8.1.1.1.2 J7.z, Fam.keep L7 hP8' g8.1.1.2 J7.w'',
    Fam.keep L7 hP8' g8.1.2 J7.w', HFam.keep L7 hP8' g8.2 hh7, ?_⟩, ?_⟩
  · rw [hP8'.pa (sc_bases _), hm8, Mem.readW_writeW_self64, ho7, onesSum_succ]
    have he7' : ((s7.gpr .x0).setWidth 32).toNat = hintOnes [Hv p σ (p.ℓ * t) i] := he7
    have ea : (s7.gpr .x0).setWidth 32 = BitVec.ofNat 32 (hintOnes [Hv p σ (p.ℓ * t) i]) := by
      apply BitVec.eq_of_toNat_eq; rw [he7', BitVec.toNat_ofNat]; omega
    have hlt : onesSum (Hv p σ (p.ℓ * t)) i + hintOnes [Hv p σ (p.ℓ * t) i] < 2 ^ 32 := by omega
    rw [ea, ← BitVec.ofNat_add, sw_ofNat hlt]
  · have e8 : s8.gpr .x24 = s3.gpr .x24 := by
      rw [hcs8, hcs7, hcs6, hcs5, hcs4]
    rw [e8, h3]
    exact bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
      fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩

/-! ## `ω` -/

theorem sign_bit {S w : Nat} (hS : S < 2 ^ 32) (hw : w < 2 ^ 31) :
    ((BitVec.ofNat 64 S - BitVec.ofNat 64 w) >>> 63).setWidth 32 = if S < w then 1 else 0 := by
  by_cases h : S < w
  · rw [ifp h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  · rw [ifn h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-! ## The checks -/

/-- Iteration `t` after `SampleInBall` succeeded. -/
structure KA (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : ICw p D σ t p.k s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t)
  cc : Pl s 0 (toRq (cV p σ (p.ℓ * t)))
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome

/-- Iteration `t` passed: `c̃`, `z` and `h`, and `CNT = 1`. -/
structure EP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p D σ s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t)
  z : Fam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t))
  h : HFam s 5 p.k (Hv p σ (p.ℓ * t))
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  pass : PassV p σ (p.ℓ * t)
  x24 : s.gpr .x24 = 1
  cnt : s.mem.readW (pa s (sc oCNT)) 64 = 1
  t_lt : t < 814
  rej : RejT p σ t

/-- Iteration `t` was rejected: `κ = ℓ(t + 1)`, `CNT = 814 - t`. -/
structure EF (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p D σ s
  kap : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 (p.ℓ * (t + 1))
  cnt : s.mem.readW (pa s (sc oCNT)) 64 = BitVec.ofNat 64 (814 - t)
  some : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  fail : ¬ PassV p σ (p.ℓ * t)
  x24 : s.gpr .x24 = 0
  t_lt : t < 814
  rej : RejT p σ t

/-- What the checks need of the layout. -/
def ksChk (p : Params) : Bool :=
  ipChkS (sgR p) (sgW p) cP && icwChk p [(cP, 1024), (sc oPS, 1024)] p.k &&
    keepB (sgB p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) && inB (sgW p) (sc oONES) 8 &&
    kbChk p [(sc oONES, 8)] && famChk (sgB p) [(sc oONES, 8)] (yBase p) p.ℓ &&
    famChk (sgB p) [(sc oONES, 8)] (wBase p) p.k &&
    (List.range p.ℓ).all (zChk p) && (List.range p.k).all (rChk p) && (List.range p.k).all (hChk2 p) &&
    inB (sgB p) (sc oONES) 8 && inB (sgW p) (sc oCNT) 8 && inB (sgW p) (sc oKAP) 8 &&
    kbChk p [] &&
    famChk (sgB p) [(sc oCNT, 8)] (yBase p) p.ℓ && famChk (sgB p) [(sc oCNT, 8)] 5 p.k &&
    famChk (sgB p) [] (yBase p) p.ℓ && famChk (sgB p) [] 5 p.k &&
    ikChk p [(sc oCNT, 8)] && ikChk p [(sc oKAP, 8)] && keepB (sgB p) [(sc oKAP, 8)] (sc oCNT) 8 &&
    keepB (sgB p) [(sc oCNT, 8)] (sc oCT) (cLen p) && decide (p.ω + 1 < 4096) && decide (p.ℓ < 4096) &&
    decide (256 * p.k < 2 ^ 32) && decide (0 < p.ℓ) && famChk (sgB p) [] (wBase p) p.k && inB (sgB p) (sc oKAP) 8

theorem bit_ne {a : Prop} [Decidable a] : (bit a).setWidth 32 ≠ 0 ↔ a := by
  by_cases ha : a
  · rw [show bit a = 1 from ifp ha _ _]; exact ⟨fun _ => ha, fun _ => by decide⟩
  · rw [show bit a = 0 from ifn ha _ _]; exact ⟨fun h => absurd rfl h, fun h => absurd h ha⟩

theorem bit_and' {a b : Prop} [Decidable a] [Decidable b] :
    BitVec.setWidth 64 ((bit a).setWidth 32 &&& (if b then (1 : BitVec 32) else 0)) = bit (a ∧ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [bit, ha, hb]

theorem passV_iff {p : Params} {σ : State} {κ : Nat} :
    (((ZOk p σ κ ∧ R0Ok p σ κ) ∧ ∀ j < p.k, normRq [CT0v p σ κ j] < p.γ₂) ∧ onesSum (Hv p σ κ) p.k < p.ω + 1) ↔
      PassV p σ κ :=
  ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, Nat.le_of_lt_succ d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, Nat.lt_succ_of_le d⟩⟩

theorem ksChk_spec {p : Params} (hc : ksChk p = true) : ∀ {Q : Prop}, (ipChkS (sgR p) (sgW p) cP = true →
    icwChk p [(cP, 1024), (sc oPS, 1024)] p.k = true →
    keepB (sgB p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) = true → inB (sgW p) (sc oONES) 8 = true →
    kbChk p [(sc oONES, 8)] = true → famChk (sgB p) [(sc oONES, 8)] (yBase p) p.ℓ = true →
    famChk (sgB p) [(sc oONES, 8)] (wBase p) p.k = true →
    (∀ r < p.ℓ, zChk p r = true) → (∀ i < p.k, rChk p i = true) → (∀ i < p.k, hChk2 p i = true) →
    inB (sgB p) (sc oONES) 8 = true → inB (sgW p) (sc oCNT) 8 = true → inB (sgW p) (sc oKAP) 8 = true →
    kbChk p [] = true → famChk (sgB p) [(sc oCNT, 8)] (yBase p) p.ℓ = true →
    famChk (sgB p) [(sc oCNT, 8)] 5 p.k = true → famChk (sgB p) [] (yBase p) p.ℓ = true →
    famChk (sgB p) [] 5 p.k = true → ikChk p [(sc oCNT, 8)] = true → ikChk p [(sc oKAP, 8)] = true →
    keepB (sgB p) [(sc oKAP, 8)] (sc oCNT) 8 = true → keepB (sgB p) [(sc oCNT, 8)] (sc oCT) (cLen p) = true →
    p.ω + 1 < 4096 → p.ℓ < 4096 → 256 * p.k < 2 ^ 32 → 0 < p.ℓ → famChk (sgB p) [] (wBase p) p.k = true →
    inB (sgB p) (sc oKAP) 8 = true → Q) → Q := by
  intro Q k
  simp only [ksChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, hz⟩, hr⟩, hh⟩, c8⟩, c9⟩, c10⟩, c13⟩, c14⟩, c15⟩, c16⟩, c17⟩, c18⟩, c19⟩, c20⟩, c21⟩, hω⟩, hl⟩, hk⟩, hl0⟩, c22⟩, c23⟩ := hc
  exact k c1 c2 c3 c4 c5 c6 c7 hz hr hh c8 c9 c10 c13 c14 c15 c16 c17 c18 c19 c20 c21 hω hl hk hl0 c22 c23

/-- The checks, after `ĉ = NTT(c)`. -/
structure KN (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : KB p D σ t s
  y : Fam s (yBase p) p.ℓ (Yv p σ (p.ℓ * t))
  w : Fam s (wBase p) p.k (Wv p σ (p.ℓ * t))

theorem cntt_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : ksChk p = true) {σ : State} {t : Nat}
    {s : State} (h : KA p D σ t s) : WP isa (nttAt P cP) s (KN p D σ t) := by
  refine ksChk_spec hc fun c1 c2 c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have L := h.c.l.st.lay
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt L c1 h.cc.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_
  rw [h.cc.2] at hq1
  have I1 := h.c.step hP1 c2
  exact ⟨⟨I1.l, by rw [L.keepBytes hP1 c3, h.ct], by
    show PolyIs _ _ _; rw [hP1.pa (by decide)]; exact hq1, h.some⟩, I1.y, I1.w⟩

/-- `x24 ← 1`, `ONES ← 0`. -/
abbrev kInit : List Instr := [.movz .x .x24 1 0] ++ setQ (sc oONES) 0

theorem kInit_ok {D : Nat} {p : Params} (hc : ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : KN p D σ t s) : WP isa (.block kInit) s (IZ p D σ t 0) := by
  refine ksChk_spec hc fun _ _ _ c4 c5 c6 c7 _ _ _ _ _ _ c13 _ _ c16 _ _ _ _ _ _ _ _ _ c22 _ => ?_
  have L1 := h.b.l.st.lay
  rw [WP.block_append_iff]
  refine wp_movz fun s2 k2 h152 => wp_nil ?_
  have hP2 : PPostB D s s2 [] := postB24 k2 _
  have B2 := h.b.step hP2 c13
  have L2 := B2.l.st.lay
  refine WP.mono (setQ_ok L2 (by decide) (by decide) c4 (by decide)) fun s3 ⟨hP3, hcs3, hm3⟩ => ?_
  have y3 := Fam.keep L2 hP3 c6 (Fam.keep L1 hP2 c16 h.y)
  exact ⟨⟨B2.step hP3 c5, fun _ h => absurd h (Nat.not_lt_zero _), y3.zero,
    Fam.keep L2 hP3 c7 (Fam.keep L1 hP2 c22 h.w), by rw [hP3.pa (by decide), hm3, Mem.readW_writeW_self64]; rfl⟩,
    by rw [hcs3.get .x24, h152]; exact (bit_one.mpr fun _ h => absurd h (Nat.not_lt_zero _)).symm⟩

theorem IZ.ir {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : IZ p D σ t p.ℓ s) : IR p D σ t 0 s :=
  ⟨⟨h.1.b, h.1.z, fun _ h => absurd h (Nat.not_lt_zero _), h.1.w.zero, h.1.ones⟩,
    by rw [h.2]; exact bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

theorem IR.ih {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : IR p D σ t p.k s) : IH p D σ t 0 s :=
  ⟨⟨h.1.b, h.1.z, fun _ h => absurd h (Nat.not_lt_zero _), h.1.w'.zero, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h.1.ones]; rfl⟩,
    by rw [h.2]; exact bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

/-- The checks done: whether the iteration passes in `x24`. -/
structure KO (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : KB p D σ t s
  z : Fam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t))
  h : HFam s 5 p.k (Hv p σ (p.ℓ * t))
  x24 : s.gpr .x24 = bit (PassV p σ (p.ℓ * t))

theorem onesOk_ok {D : Nat} {p : Params} (hc : ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : IH p D σ t p.k s) : WP isa (.block (onesOk p)) s (KO p D σ t) := by
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ c8 _ _ c13 _ _ c16 c17 _ _ _ _ hω _ hk _ _ _ => ?_
  obtain ⟨J6, h156⟩ := h
  have L6 := J6.b.l.st.lay
  have hS := onesSum_le (Hv p σ (p.ℓ * t)) p.k
  refine WP.mono (onesOk_run p hω s (L6.inR c8)) fun s7 ⟨⟨h157, hm7⟩, k7⟩ => ?_
  rw [J6.ones, sign_bit (by omega) (by omega), h156, bit_and', bit_congr passV_iff] at h157
  have hP7 : PPostB D s s7 [] := postB_of_keep k7 (by decide) (by rw [hm7]; exact Frame.refl _ _)
  exact ⟨J6.b.step hP7 c13, Fam.keep L6 hP7 c16 J6.z, HFam.keep L6 hP7 c17 J6.h, h157⟩

theorem kBranch_ok {D : Nat} {p : Params} (hc : ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : KO p D σ t s) :
    WP isa (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p))) s fun s' => EP p D σ t s' ∨ EF p D σ t s' := by
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ _ c9 c10 _ c14 c15 _ _ c18 c19 c20 c21 _ hl _ _ _ c23 => ?_
  have B7 := h.b
  have L7 := B7.l.st.lay
  refine ifOkElse_ok (fun hne => ?_) fun he => ?_
  · rw [h.x24] at hne
    have hpass := bit_ne.mp hne
    refine WP.mono (setQ_ok L7 (by decide) (by decide) c9 (by decide)) fun s9 ⟨hP9, hcs9, hm9⟩ => ?_
    exact .inl ⟨B7.l.k.step hP9 c18, by rw [L7.keepBytes hP9 c21, B7.ct],
      Fam.keep L7 hP9 c14 h.z, HFam.keep L7 hP9 c15 h.h, B7.some,
      hpass, by rw [hcs9.get .x24, h.x24]; exact bit_one.mpr hpass,
      by rw [hP9.pa (by decide), hm9, Mem.readW_writeW_self64]; rfl, B7.l.t_lt, B7.l.rej⟩
  · rw [h.x24] at he
    have hfail : ¬ PassV p σ (p.ℓ * t) := fun hp => (bit_ne.mpr hp) he
    refine WP.mono (kapAdd_ok p hl s (L7.inW c10) (L7.inR c23)) fun s9 ⟨hm9, k9⟩ => ?_
    have hf : Frame [⟨pa s (sc oKAP), 8⟩] s.mem s9.mem := by
      rw [hm9]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hP9' : PPostB D s s9 [(sc oKAP, 8)] := postB_of_keep k9 (by decide) hf
    refine .inr ⟨B7.l.k.step hP9' c19, ?_, by rw [L7.keepW hP9' c20, B7.l.cnt], B7.some, hfail,
      by rw [k9.get .x24, h.x24]; exact bit_zero.mpr hfail, B7.l.t_lt, B7.l.rej⟩
    rw [hP9'.pa (by decide), hm9, Mem.readW_writeW_self64, B7.l.kap, ofNat64_add, Nat.mul_succ]

theorem checks_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : ksChk p = true) {σ : State} {t : Nat}
    {s : State} (h : KA p D σ t s) :
    WP isa (checks P p) s fun s' => EP p D σ t s' ∨ EF p D σ t s' := by
  refine ksChk_spec hc fun _ _ _ _ _ _ _ hz hr hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  unfold checks
  refine WP.seq (WP.mono (cntt_ok hP hc h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (kInit_ok hc h1) fun s3 I3 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun r => IZ p D σ t r) p.ℓ 0 (fun r _ hr s hs => zR_ok hP (hz r (by omega)) hs)
    s3 I3) fun s4 hs4 => ?_)
  rw [Nat.zero_add] at hs4
  refine WP.seq (WP.mono (seqR_ok (I := fun i => IR p D σ t i) p.k 0 (fun i _ hi s hs => r0R_ok hP (hr i (by omega)) hs)
    s4 hs4.ir) fun s5 hs5 => ?_)
  rw [Nat.zero_add] at hs5
  refine WP.seq (WP.mono (seqR_ok (I := fun i => IH p D σ t i) p.k 0 (fun i _ hi s hs => hR_ok hP (hh i (by omega)) hs)
    s5 hs5.ih) fun s6 hs6 => ?_)
  rw [Nat.zero_add] at hs6
  exact WP.seq (WP.mono (onesOk_ok hc hs6) fun s7 h7 => kBranch_ok hc h7)

theorem ksChk_ok {p : Params} (h : Ok3 p) : ksChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem bChk_ok {p : Params} (h : Ok3 p) : bChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Sign
