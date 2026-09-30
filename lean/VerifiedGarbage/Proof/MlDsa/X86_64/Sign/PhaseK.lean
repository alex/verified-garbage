import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseC
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# ML-DSA signing on x86-64: the checks of an iteration

Untrusted: everything here is checked by Lean. `c = SampleInBall(c̃)` at
`ĉ` (`ball_ok`), and, if it succeeded, `ĉ = NTT(c)` and each check of the
iteration, their results ANDed into `r15`: the norm of each `z[r]`
(`zR_ok`), of each `r₀[i]` (`r0R_ok`) and of each `ct₀[i]`, with each
hint `h[i]` and the number of its 1s summed at `ONES` (`hR_ok`), and that
sum against `ω` (`onesOk_ok`); so `r15` is 1 exactly when the iteration
passes (`checks_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
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
  r01 : (s.gpr .rax).setWidth 32 = 0 ∨ (s.gpr .rax).setWidth 32 = 1
  ok : (s.gpr .rax).setWidth 32 = 1 → Pl s 0 (toRq (cV p σ (p.ℓ * t))) ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome
  bad : (s.gpr .rax).setWidth 32 = 0 → sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none

def bChk (p : Params) : Bool :=
  ballChk (sgB p) (sgW p) (cLen p) cP && icwChk p [(cP, 1024), (sc oPS, 2048)] p.k &&
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

/-! ## Norms, into `r15` -/

theorem normAt_okB {P : Prims} {D : Nat} (hP : PrimsOk P D) {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay D rbs wbs s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : normChk (rbs ++ wbs) f = true)
    (hr : Reduced s.mem (pa s f)) {a : Prop} [Decidable a] (h15 : s.gpr .r15 = bit a) :
    WP isa (normAt P f B) s fun s' => PPostB D s s' [] ∧ (∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r15 = bit (a ∧ normRq [polyAt s.mem (pa s f)] < B) := by
  refine WP.seq (WP.mono (normCall_ok hP L hB hc hr) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  refine WP.mono (and15_ok s1) fun s2 ⟨h15', hm2, k2⟩ => ?_
  obtain ⟨hP2, hcs2⟩ := postB15 (D := D) k2 hm2 (([] : List (Ptr × Nat)).map (toR s1))
  refine ⟨PPostB.trans hP1 hP2 (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil), fun r hr hne => (hcs2 r hr hne).trans (hcs1 r hr), ?_⟩
  rw [h15', bit_and (hcs1 _ (by decide) |>.trans h15) hq1]

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

/-- The checks of `z[j]` for `j < r`, with `ONES = 0` (but `r15`). -/
structure IZb (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  b : KB p D σ t s
  z : Fam s (yBase p) r (Zv p σ (p.ℓ * t))
  y : Fam s (yBase p + r) (p.ℓ - r) fun j => Yv p σ (p.ℓ * t) (r + j)
  w : Fam s (wBase p) p.k (Wv p σ (p.ℓ * t))
  ones : s.mem.readW (pa s (sc oONES)) 64 = 0

/-- The checks of `z[j]` for `j < r`, their results in `r15`. -/
def IZ (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop :=
  IZb p D σ t r s ∧ s.gpr .r15 = bit (∀ j < r, normRq [Zv p σ (p.ℓ * t) j] < p.γ₁ - p.β)

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
  mulChk (sgB p) (sgW p) t1P cP (s1P p r) && ipChk (sgB p) (sgW p) t1P && accChk (sgB p) (sgW p) (yP p r) t1P &&
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
  have e15 : s3.gpr .r15 = s.gpr .r15 := by
    rw [hcs3 _ (by decide), hcs2 _ (by decide), hcs1 _ (by decide)]
  refine WP.mono (normAt_okB hP J3.b.l.st.lay hB cn hz3.1 (e15.trans h15)) fun s4 ⟨hP4, _, h4⟩ => ?_
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
    s.gpr .r15 = bit (ZOk p σ (p.ℓ * t) ∧ ∀ j < i, normRq [R0v p σ (p.ℓ * t) j] < p.γ₂ - p.β)

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
  mulChk (sgB p) (sgW p) t1P cP (s2P p i) && ipChk (sgB p) (sgW p) t1P && accChk (sgB p) (sgW p) (wP p i) t1P &&
    rwChk (sgB p) (sgW p) (wP p i) 1024 t2P 1024 && normChk (sgB p) t2P && rfam p w1 i && rfam p w2 i &&
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
  have e15 : s4.gpr .r15 = s.gpr .r15 := by
    rw [hcs4 _ (by decide), hcs3 _ (by decide), hcs2 _ (by decide), hcs1 _ (by decide)]
  refine WP.mono (normAt_okB hP J4.b.l.st.lay hB cn (by rw [hP4.pa (by decide)]; exact hq4.1) (e15.trans h15))
    fun s5 ⟨hP5, _, h5⟩ => ?_
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
  rw [hP.pa (keepB_cs hk)]
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

/-- The block after `vg_mldsa_make_hint`: its result added to `ONES`. -/
abbrev onesAdd : List Instr :=
  [.mov32 .rcx (.mem (VG.Impl.MlKem.X86_64.at_ .rbx oONES)), .alu32 .add .rcx (.reg .rax),
    .store (VG.Impl.MlKem.X86_64.at_ .rbx oONES) .rcx]

theorem onesAdd_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (pa s (sc oONES)) 4)
    (h2 : InRegions s.wr (pa s (sc oONES)) 8) :
    WP isa (.block onesAdd) s fun s' => s'.mem = s.mem.writeW (pa s (sc oONES))
      (BitVec.setWidth 64 (s.mem.readW (pa s (sc oONES)) 32 + (s.gpr .rax).setWidth 32)) ∧ Keep [.rcx] s s' := by
  refine WP.keep [.rcx] ?_ (by rfl)
  xrun [h1, h2]

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
  IHb p D σ t i i s ∧ s.gpr .r15 = bit ((ZOk p σ (p.ℓ * t) ∧ R0Ok p σ (p.ℓ * t)) ∧
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
    m.readW a 32 = BitVec.ofNat 32 x := by
  have e := readW_extract m a (w := 64) (k := 0) (n := 4) (by omega)
  rw [BitVec.add_zero, h] at e
  rw [← e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  omega

/-- What `h[i]` needs of the layout. -/
def hChk2 (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t3P, 1024)]
  let w2 : List (Ptr × Nat) := [(t3P, 1024), (sc oPS, 1024)]
  let w4 : List (Ptr × Nat) := [(t4P, 1024)]
  let w5 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w7 : List (Ptr × Nat) := [(hP i, 1024)]
  let w8 : List (Ptr × Nat) := [(sc oONES, 8)]
  mulChk (sgB p) (sgW p) t3P cP (t0P p i) && ipChk (sgB p) (sgW p) t3P && normChk (sgB p) t3P &&
    copyChk (sgB p) (sgW p) t4P (wP p i) 1024 && accChk (sgB p) (sgW p) (wP p i) t3P &&
    accChk (sgB p) (sgW p) t4P (wP p i) && hintChk (sgB p) (sgW p) t4P (wP p i) (hP i) &&
    hfam p w1 i i && hfam p w2 i i && hfam p [] i i && hfam p w4 i i &&
    (kbChk p w5 && famChk (sgB p) w5 (yBase p) p.ℓ && famChk (sgB p) w5 5 i) &&
    hfam p w4 (i + 1) i && hfam p w7 (i + 1) i && hfam p w8 (i + 1) (i + 1) &&
    famChk (sgB p) w5 (wBase p) i && famChk (sgB p) w5 (wBase p + (i + 1)) (p.k - (i + 1)) &&
    keepB (sgB p) w1 (sc oONES) 8 && keepB (sgB p) w2 (sc oONES) 8 && keepB (sgB p) [] (sc oONES) 8 &&
    keepB (sgB p) w4 (sc oONES) 8 && keepB (sgB p) w5 (sc oONES) 8 && keepB (sgB p) w7 (sc oONES) 8 &&
    keepB (sgB p) [] t3P 1024 && keepB (sgB p) w4 t3P 1024 &&
    keepB (sgB p) w5 t4P 1024 && keepB (sgB p) w1 (t0P p i) 1024 &&
    inB (sgB p) (sc oONES) 4 && inB (sgW p) (sc oONES) 8 &&
    decide (p.γ₂ < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k) && decide (256 * p.k < 2 ^ 32)

theorem pa_sc {s s' : State} (h : s'.gpr .rbx = s.gpr .rbx) (o : Nat) : pa s' (sc o) = pa s (sc o) := by
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
  have b1 : s1.gpr .rbx = s.gpr .rbx := hP1.bs _ (by decide)
  -- `ct₀[i]`
  refine WP.seq (WP.mono (ipAt_ok (t := nttInv) hP.invNtt I1.b.l.st.lay ci (by rw [pa_sc b1]; exact hq1.1))
    fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [pa_sc b1, hq1.2] at hq2
  have I2 := I1.step hP2 g2 o2
  have b2 : s2.gpr .rbx = s.gpr .rbx := (hP2.bs _ (by decide)).trans b1
  have q2 : Pl s2 3 (CT0v p σ (p.ℓ * t) i) := by show PolyIs _ _ _; rw [pa_sc b2]; exact hq2
  -- its norm
  have e2 : s2.gpr .r15 = s.gpr .r15 := by rw [hcs2 _ (by decide), hcs1 _ (by decide)]
  refine WP.seq (WP.mono (normAt_okB hP I2.b.l.st.lay hγ' cn q2.1 (e2.trans h15)) fun s3 ⟨hP3, hcs3, h3⟩ => ?_)
  rw [q2.2] at h3
  have I3 := I2.step hP3 g3 o3
  have q3 : Pl s3 3 (CT0v p σ (p.ℓ * t) i) := I2.b.l.st.lay.keepPoly hP3 t3 q2
  -- `T4 ← w[i] - cs₂[i]`
  have hw3 : Pl s3 (wBase p + i) (W'v p σ (p.ℓ * t) i) := I3.w' 0 (by omega)
  refine WP.seq (WP.mono (copy_okB I3.b.l.st.lay cc) fun s4 ⟨hP4, hcs4, hb4⟩ => ?_)
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
  have ho7 : s7.mem.readW (pa s7 (sc oONES)) 32 = BitVec.ofNat 32 (onesSum (Hv p σ (p.ℓ * t)) i) := ones32 J7.ones
  have L7 := J7.b.l.st.lay
  refine WP.mono (onesAdd_ok s7 (L7.iR i1) (L7.iW i2)) fun s8 ⟨hm8, k8⟩ => ?_
  have hf : Frame [⟨pa s7 (sc oONES), 8⟩] s7.mem s8.mem := by
    rw [hm8]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨hP8, hcs8⟩ := postB_of_keep (D := D) k8 (by decide) hf
  have hP8' : PPostB D s7 s8 [(sc oONES, 8)] := hP8
  simp only [hfam, Bool.and_eq_true] at g8
  have hS := onesSum_le (Hv p σ (p.ℓ * t)) i
  have hS1 := hintOnes_le (Hv p σ (p.ℓ * t) i)
  have hik : 256 * (i + 1) ≤ 256 * p.k := Nat.mul_le_mul_left _ hi
  refine ⟨⟨J7.b.step hP8' g8.1.1.1.1, Fam.keep L7 hP8' g8.1.1.1.2 J7.z, Fam.keep L7 hP8' g8.1.1.2 J7.w'',
    Fam.keep L7 hP8' g8.1.2 J7.w', HFam.keep L7 hP8' g8.2 hh7, ?_⟩, ?_⟩
  · rw [hP8'.pa (sc_bases _), hm8, Mem.readW_writeW_self64, ho7, onesSum_succ]
    have he7' : ((s7.gpr .rax).setWidth 32).toNat = hintOnes [Hv p σ (p.ℓ * t) i] := he7
    have ea : (s7.gpr .rax).setWidth 32 = BitVec.ofNat 32 (hintOnes [Hv p σ (p.ℓ * t) i]) := by
      apply BitVec.eq_of_toNat_eq; rw [he7', BitVec.toNat_ofNat]; omega
    have hlt : onesSum (Hv p σ (p.ℓ * t)) i + hintOnes [Hv p σ (p.ℓ * t) i] < 2 ^ 32 := by omega
    rw [ea, ← BitVec.ofNat_add, sw_ofNat hlt]
  · have e8 : s8.gpr .r15 = s3.gpr .r15 := by
      rw [hcs8 _ (by decide), hcs7 _ (by decide), hcs6 _ (by decide), hcs5 _ (by decide), hcs4 _ (by decide)]
    rw [e8, h3]
    exact bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
      fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩

/-! ## `ω` -/

theorem onesOk_run (p : Params) (hω : p.ω + 1 < 2 ^ 31) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (pa s (sc oONES)) 4) :
    WP isa (.block (onesOk p)) s fun s' => (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
      ((BitVec.setWidth 64 (s.mem.readW (pa s (sc oONES)) 32) - BitVec.ofNat 64 (p.ω + 1)) >>> 63).setWidth 32) ∧
      s'.mem = s.mem) ∧ Keep [.rax, .r15] s s' := by
  refine WP.keep [.rax, .r15] ?_ (by rfl)
  unfold onesOk
  xrun [h1, sx_ofNat hω]

theorem sign_bit {S w : Nat} (hS : S < 2 ^ 32) (hw : w < 2 ^ 31) :
    ((BitVec.setWidth 64 (BitVec.ofNat 32 S) - BitVec.ofNat 64 w) >>> 63).setWidth 32 = if S < w then 1 else 0 := by
  rw [sw_ofNat hS]
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
  r15 : s.gpr .r15 = 1
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
  r15 : s.gpr .r15 = 0
  t_lt : t < 814
  rej : RejT p σ t

/-- What the checks need of the layout. -/
def ksChk (p : Params) : Bool :=
  ipChk (sgB p) (sgW p) cP && icwChk p [(cP, 1024), (sc oPS, 1024)] p.k &&
    keepB (sgB p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) && inB (sgW p) (sc oONES) 8 &&
    kbChk p [(sc oONES, 8)] && famChk (sgB p) [(sc oONES, 8)] (yBase p) p.ℓ &&
    famChk (sgB p) [(sc oONES, 8)] (wBase p) p.k &&
    (List.range p.ℓ).all (zChk p) && (List.range p.k).all (rChk p) && (List.range p.k).all (hChk2 p) &&
    inB (sgB p) (sc oONES) 4 && inB (sgW p) (sc oCNT) 8 && inB (sgW p) (sc oKAP) 8 &&
    kbChk p [] &&
    famChk (sgB p) [(sc oCNT, 8)] (yBase p) p.ℓ && famChk (sgB p) [(sc oCNT, 8)] 5 p.k &&
    famChk (sgB p) [] (yBase p) p.ℓ && famChk (sgB p) [] 5 p.k &&
    ikChk p [(sc oCNT, 8)] && ikChk p [(sc oKAP, 8)] && keepB (sgB p) [(sc oKAP, 8)] (sc oCNT) 8 &&
    keepB (sgB p) [(sc oCNT, 8)] (sc oCT) (cLen p) && decide (p.ω + 1 < 2 ^ 31) && decide (p.ℓ < 2 ^ 31) &&
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

theorem checks_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : ksChk p = true) {σ : State} {t : Nat}
    {s : State} (h : KA p D σ t s) :
    WP isa (checks P p) s fun s' => EP p D σ t s' ∨ EF p D σ t s' := by
  simp only [ksChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, hz⟩, hr⟩, hh⟩, c8⟩, c9⟩, c10⟩, c13⟩, c14⟩, c15⟩, c16⟩, c17⟩, c18⟩, c19⟩, c20⟩, c21⟩, hω⟩, hl⟩, hk⟩, hl0⟩, c22⟩, c23⟩ := hc
  have L := h.c.l.st.lay
  unfold checks
  -- `ĉ = NTT(c)`
  refine WP.seq (WP.mono (ipAt_ok (t := ntt) hP.ntt L c1 h.cc.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.cc.2] at hq1
  have I1 := h.c.step hP1 c2
  have B1 : KB p D σ t s1 := ⟨I1.l, by rw [L.keepBytes hP1 c3, h.ct], by
    show PolyIs _ _ _; rw [hP1.pa (by decide)]; exact hq1, h.some⟩
  have L1 := B1.l.st.lay
  -- `r15 ← 1`, `ONES ← 0`
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r15] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .r15 = 1) (by xrun) (by decide))
    fun s2 ⟨⟨hm2, h152⟩, k2⟩ => ?_
  have hP2 : PPostB D s1 s2 [] := (postB15 k2 hm2 _).1
  have B2 := B1.step hP2 c13
  have L2 := B2.l.st.lay
  refine WP.mono (setQ_okB L2 (by decide) (by decide) c4) fun s3 ⟨hP3, hcs3, hm3⟩ => ?_
  have y3 := Fam.keep L2 hP3 c6 (Fam.keep L1 hP2 c16 I1.y)
  have I3 : IZ p D σ t 0 s3 := ⟨⟨B2.step hP3 c5, fun _ h => absurd h (Nat.not_lt_zero _),
    y3.zero,
    Fam.keep L2 hP3 c7 (Fam.keep L1 hP2 c22 I1.w), by rw [hP3.pa (by decide), hm3, Mem.readW_writeW_self64]; rfl⟩,
    by rw [hcs3 _ (by decide), h152]; exact (bit_one.mpr fun _ h => absurd h (Nat.not_lt_zero _)).symm⟩
  -- `z`
  refine WP.seq (WP.mono (seqR_ok (I := fun r => IZ p D σ t r) p.ℓ 0 (fun r _ hr s hs => zR_ok hP (hz r (by omega)) hs)
    s3 I3) fun s4 hs4 => ?_)
  rw [Nat.zero_add] at hs4
  have I4 : IR p D σ t 0 s4 := ⟨⟨hs4.1.b, hs4.1.z, fun _ h => absurd h (Nat.not_lt_zero _),
    hs4.1.w.zero, hs4.1.ones⟩,
    by rw [hs4.2]; exact bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩
  -- `r₀`
  refine WP.seq (WP.mono (seqR_ok (I := fun i => IR p D σ t i) p.k 0 (fun i _ hi s hs => r0R_ok hP (hr i (by omega)) hs)
    s4 I4) fun s5 hs5 => ?_)
  rw [Nat.zero_add] at hs5
  have I5 : IH p D σ t 0 s5 := ⟨⟨hs5.1.b, hs5.1.z, fun _ h => absurd h (Nat.not_lt_zero _),
    hs5.1.w'.zero, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [hs5.1.ones]; rfl⟩,
    by rw [hs5.2]; exact bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩
  -- `ct₀` and `h`
  refine WP.seq (WP.mono (seqR_ok (I := fun i => IH p D σ t i) p.k 0 (fun i _ hi s hs => hR_ok hP (hh i (by omega)) hs)
    s5 I5) fun s6 hs6 => ?_)
  rw [Nat.zero_add] at hs6
  obtain ⟨J6, h156⟩ := hs6
  have L6 := J6.b.l.st.lay
  -- `ONES ≤ ω`
  have hS := onesSum_le (Hv p σ (p.ℓ * t)) p.k
  refine WP.seq (WP.mono (onesOk_run p hω s6 (L6.iR c8)) fun s7 ⟨⟨h157, hm7⟩, k7⟩ => ?_)
  rw [ones32 J6.ones, sign_bit (by omega) (by omega), h156, bit_and', bit_congr passV_iff] at h157
  have hP7 : PPostB D s6 s7 [] := ⟨k7.2.1, k7.2.2, fun r hr => k7.gpr (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k7.gpr (by decide),
      by rw [hm7]; exact Frame.refl _ _⟩
  have B7 := J6.b.step hP7 c13
  have z7 := Fam.keep L6 hP7 c16 J6.z
  have h7 := HFam.keep L6 hP7 c17 J6.h
  have L7 := B7.l.st.lay
  refine ifOkElse_ok (D := D) (fun s8 hP8 hcs8 hm8 hne => ?_) fun s8 hP8 hcs8 hm8 he => ?_
  · rw [h157] at hne
    have hpass := bit_ne.mp hne
    have B8 := B7.step hP8 c13
    have L8 := B8.l.st.lay
    refine WP.mono (setQ_okB L8 (by decide) (by decide) c9) fun s9 ⟨hP9, hcs9, hm9⟩ => ?_
    exact .inl ⟨B8.l.k.step hP9 c18, by rw [L8.keepBytes hP9 c21, B8.ct],
      Fam.keep L8 hP9 c14 (Fam.keep L7 hP8 c16 z7), HFam.keep L8 hP9 c15 (HFam.keep L7 hP8 c17 h7), B8.some,
      hpass, by rw [hcs9 _ (by decide), hcs8 _ (by decide), h157]; exact bit_one.mpr hpass,
      by rw [hP9.pa (by decide), hm9, Mem.readW_writeW_self64]; rfl, B8.l.t_lt, B8.l.rej⟩
  · rw [h157] at he
    have hfail : ¬ PassV p σ (p.ℓ * t) := fun hp => (bit_ne.mpr hp) he
    have B8 := B7.step hP8 c13
    have L8 := B8.l.st.lay
    refine WP.mono (addQ_ok (sc oKAP) p.ℓ (by decide) hl s8 (L8.iW c10) (L8.iR c23)) fun s9 ⟨hm9, k9⟩ => ?_
    have hf : Frame [⟨pa s8 (sc oKAP), 8⟩] s8.mem s9.mem := by
      rw [hm9]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain ⟨hP9, hcs9⟩ := postB_of_keep (D := D) k9 (by decide) hf
    have hP9' : PPostB D s8 s9 [(sc oKAP, 8)] := hP9
    refine .inr ⟨B8.l.k.step hP9' c19, ?_, by rw [L8.keepW hP9' c20, B8.l.cnt], B8.some, hfail,
      by rw [hcs9 _ (by decide), hcs8 _ (by decide), h157]; exact bit_zero.mpr hfail, B8.l.t_lt, B8.l.rej⟩
    rw [hP9'.pa (by decide), hm9, Mem.readW_writeW_self64, B8.l.kap, ofNat64_add, Nat.mul_succ]

theorem ksChk_ok {p : Params} (h : Ok3 p) : ksChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem bChk_ok {p : Params} (h : Ok3 p) : bChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.X86_64.Sign
