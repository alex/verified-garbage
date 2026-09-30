import VerifiedGarbage.Proof.MlDsa.X86.Sign.Run

/-!
# ML-DSA signing on x86 (32-bit): the checks of an iteration

Untrusted: everything here is checked by Lean. Once `SampleInBall`
succeeded (`ballCall_piece`), the checks (`CS`: what they keep, with `y`,
`w`, the hint, `OK` and `ONES` as far as they got) compute `z` in place of
`y` (`zR_piece`), `w - cs₂` in place of `w` and the norm of its `LowBits`
(`r0R_piece`), and `ct₀`, `w - cs₂ + ct₀` and the hint (`hR_piece`); `OK`
is then 1 exactly when the checks pass (`onesOk_piece`, `pass_iff`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_shr)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

section
variable (p : Params)

/-- `c`, and the values of the checks, of the iteration with counter `κ`. -/
abbrev Cv (s₀ : State) (κ : Nat) : IPoly := cV p (skOf p s₀) (muOf s₀) (rndOf s₀) κ
abbrev Zv (s₀ : State) (κ r : Nat) : Poly := zF p (S1 p s₀) (rppS p s₀) κ (Cv p s₀ κ) r
abbrev W'v (s₀ : State) (κ i : Nat) : Poly := w'F p (Am p s₀) (S2 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i
abbrev R0v (s₀ : State) (κ i : Nat) : Poly := r0F p (Am p s₀) (S2 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i
abbrev CT0v (s₀ : State) (κ i : Nat) : Poly := ct0F (T0 p s₀) (Cv p s₀ κ) i
abbrev W''v (s₀ : State) (κ i : Nat) : Poly := w''F p (Am p s₀) (S2 p s₀) (T0 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i
abbrev Hv (s₀ : State) (κ i : Nat) : Vector Bool n := hF p (Am p s₀) (S2 p s₀) (T0 p s₀) (rppS p s₀) κ (Cv p s₀ κ) i

/-- The checks of the first `r` polynomials. -/
def okZ (s₀ : State) (κ r : Nat) : Bool := (List.range r).all fun j => decide (normRq [Zv p s₀ κ j] < p.γ₁ - p.β)
def okR (s₀ : State) (κ i : Nat) : Bool := (List.range i).all fun j => decide (normRq [R0v p s₀ κ j] < p.γ₂ - p.β)
def okT (s₀ : State) (κ i : Nat) : Bool := (List.range i).all fun j => decide (normRq [CT0v p s₀ κ j] < p.γ₂)
/-- The number of 1s of the first `i` polynomials of the hint. -/
def onesS (s₀ : State) (κ i : Nat) : Nat := ((List.range i).map fun j => hintOnes [Hv p s₀ κ j]).sum

end

theorem all_range_succ {f : Nat → Bool} {r : Nat} :
    (List.range (r + 1)).all f = ((List.range r).all f && f r) := by
  simp only [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem all_range_iff {f : Nat → Prop} [DecidablePred f] {r : Nat} :
    (List.range r).all (fun j => decide (f j)) = true ↔ ∀ j < r, f j := by
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-- The checks pass exactly when `OK` ends up 1. -/
theorem pass_iff {s₀ : State} {κ : Nat} :
    passV p (skOf p s₀) (muOf s₀) (rndOf s₀) κ ↔
      (okZ p s₀ κ p.ℓ && okR p s₀ κ p.k && okT p s₀ κ p.k && decide (onesS p s₀ κ p.k ≤ p.ω)) = true := by
  simp only [Bool.and_eq_true, okZ, okR, okT, all_range_iff, onesS, passV, passF, and_assoc]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, decide_eq_true d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, of_decide_eq_true d⟩⟩

/-! ## The hint -/

/-- The first `nh` polynomials of the hint, in the slots from 5. -/
def HF (s₀ : State) (m : Mem) (nh : Nat) (f : Nat → Vector Bool n) : Prop :=
  ∀ j < nh, HintIs m (Buf.addr s₀ (pS (5 + j))) 1 [f j]

theorem hintIs_congr {m m' : Mem} {a : Addr} {h : Vector Bool n}
    (e : ∀ x < 1024, m' (a + BitVec.ofNat 64 x) = m (a + BitVec.ofNat 64 x)) (hh : HintIs m a 1 [h]) :
    HintIs m' a 1 [h] := by
  refine ⟨hh.1, fun i hi j hj => ?_⟩
  have : coeffAt m' a (256 * i + j) = coeffAt m a (256 * i + j) := by
    unfold coeffAt
    refine Mem.readW_congr fun t ht => ?_
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact e _ (by have : n = 256 := rfl; omega)
  rw [this]; exact hh.2 i hi j hj

theorem HF.keep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {nh : Nat} (hn : 5 + nh ≤ nS p)
    (h : ∀ c ∈ bs, Out p (oP 5) (oP (5 + nh)) c) {f : Nat → Vector Bool n} (hf : HF s₀ m nh f) : HF s₀ m' nh f :=
  fun j hj => hintIs_congr (VG.Proof.MlKem.X86.Top.keep hp (N := N) (by show N + 16 ≤ 96; omega)
    (apart_of (slot_ok' ps (by omega)) rfl fun c hc => by
      obtain ⟨h₁, h₂⟩ := h c hc
      exact ⟨h₁, fun e => by simp only [oP] at h₂ ⊢; have := h₂ e; omega⟩) fr) (hf j hj)

theorem HF.snoc {s₀ : State} {m : Mem} {nh : Nat} {f : Nat → Vector Bool n} (h : HF s₀ m nh f)
    (h' : HintIs m (Buf.addr s₀ (pS (5 + nh))) 1 [f nh]) : HF s₀ m (nh + 1) f := fun j hj => by
  by_cases e : j < nh
  · exact h j e
  · rw [show j = nh by omega]; exact h'

/-- Slot `r` of a family changed, the others kept. -/
theorem Fam.upd {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {b n r : Nat} (hb : b + n ≤ nS p) (hr : r < n)
    (h : ∀ c ∈ bs, Out p (oP b) (oP (b + r)) c ∧ Out p (oP (b + r + 1)) (oP (b + n)) c) {f g : Nat → Poly}
    (hf : Fam s₀ m b n f) (hv : PolyIs m' (Buf.addr s₀ (pS (b + r))) (g r)) (hg : ∀ j < n, j ≠ r → g j = f j) :
    Fam s₀ m' b n g := fun j hj => by
  by_cases e : j = r
  · subst e; exact hv
  · rw [hg j hj e]
    exact keepP hp ps hN fr (by omega) (fun c hc => by
      obtain ⟨⟨h₁, h₂⟩, -, h₃⟩ := h c hc
      exact ⟨h₁, fun ea => by
        have := h₂ ea; have := h₃ ea; simp only [oP] at *
        rcases (by omega : j < r ∨ r < j) with hj' | hj' <;> omega⟩) (hf j hj)

/-! ## The state of the checks -/

/-- The checks of iteration `t`, with `y`, `w`, the first `nh` polynomials of
the hint, `OK` and `ONES` as `fY`, `fW`, `okb` and `ones` say. -/
structure CS (p : Params) (t : Nat) (fY fW : State → Nat → Poly) (nh : Nat) (okb : State → Bool)
    (ones : State → Nat) (s₀ s : State) : Prop where
  it : IT p t s₀ s
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t)
  c : PolyIs s.mem (Buf.addr s₀ cP) (chF (Cv p s₀ (p.ℓ * t)))
  fy : Fam s₀ s.mem (yB p) p.ℓ (fY s₀)
  fw : Fam s₀ s.mem (wB p) p.k (fW s₀)
  fh : HF s₀ s.mem nh (Hv p s₀ (p.ℓ * t))
  ok : scw s₀ s oOK = if okb s₀ then 1 else 0
  ones : scw s₀ s oONES = BitVec.ofNat 32 (ones s₀)
  nh : nh ≤ p.k

section
variable {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
  {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
  {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
include hp ps h c' hN fr

omit c' in
theorem CS.ct_keep (hb : ∀ c ∈ bs, Out p oCT (oCT + 64) c) :
    bytesAt s'.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * t) := by
  have := ps.hcLen
  rw [keepB hp hN fr (by ofs) fun c hc => ⟨(hb c hc).1, fun e => by
    have := (hb c hc).2 e; simp only [oCT] at this ⊢; omega⟩, h.ct]

theorem CS.keep (hb : ∀ c ∈ bs, OutC p nh c) : CS p t fY fW nh okb ones s₀ s' := by
  have := h.nh
  exact ⟨h.it.keep hp ps c' hN fr fun c hc => (hb c hc).1, h.ct_keep hp ps hN fr fun c hc => (hb c hc).2.2.1,
    keepP hp ps hN fr (j := 0) (by simp only [nS]; omega) (fun c hc => (hb c hc).2.1) h.c,
    h.fy.keep hp ps hN fr (by simp only [nS, yB]; omega) fun c hc => ⟨(hb c hc).2.2.2.1.1, fun e => by
      have := (hb c hc).2.2.2.1.2 e; simp only [oP, yB, wB] at this ⊢; omega⟩,
    h.fw.keep hp ps hN fr (by simp only [nS, wB]; omega) fun c hc => ⟨(hb c hc).2.2.2.1.1, fun e => by
      have := (hb c hc).2.2.2.1.2 e; simp only [oP, yB, wB] at this ⊢; omega⟩,
    h.fh.keep hp ps hN fr (by simp only [nS]; omega) fun c hc => (hb c hc).2.2.2.2.1,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2.2.2.2.1]; exact h.ok,
    by rw [scw, keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => (hb c hc).2.2.2.2.2.2]; exact h.ones,
    h.nh⟩

end

/-! ## `SampleInBall` -/

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

/-- After `SampleInBall` in iteration `t`. -/
structure IB (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  cc : CC p t s₀ s
  run : Run p F t s₀
  eax : s.gpr .eax = if F.ballF p.τ (CTv p s₀ (p.ℓ * t)) then 1 else 0
  yes : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true → PolyIs s.mem (Buf.addr s₀ cP) (toRq (Cv p s₀ (p.ℓ * t)))
  no : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = false → sampleInBall p.τ minBounds.ball (CTv p s₀ (p.ℓ * t)) = none

theorem CC.keep {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CC p t s₀ s)
    (c' : Ctx (Y p) s₀ s') {bs : List Buf} {N : Nat} (hN : N ≤ 80) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (hb : ∀ c ∈ bs, (OutI p c ∧ Out p (oP (yB p)) (oP (wB p + p.k)) c) ∧ Out p oCT (oCT + 64) c) : CC p t s₀ s' := by
  have := ps.hcLen
  exact ⟨h.cw.keep hp ps (Nat.le_refl _) c' hN fr fun c hc => (hb c hc).1, by
    rw [keepB hp hN fr (by ofs) fun c hc => ⟨(hb c hc).2.1, fun e => by
      have := (hb c hc).2.2 e; simp only [oCT] at this ⊢; omega⟩, h.ct]⟩

/-- `c = SampleInBall(c̃)` to `ĉ`'s slot. -/
theorem ballCall_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => CC p t s₀ s ∧ Run p F t s₀) (IB p F t) (ballAt P (cLen p) p.τ cP) := by
  have := ps.hcLen
  refine ball_piece F.ball (F.ok _ (by simp)) (cLen p) p.τ ps.hball SC oCT SC (oP 0) SC oPS (by ofs)
    (fun _ _ _ h => h.1.cw.cm.it.kd.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => ?_)
    fun s₀ s s' hp h c' fr heax hred hout => ?_
  · rw [h.1.ct, h'.1.ct]; exact (run_at ps hq h.2).1
  · rw [h.1.ct] at heax hout
    refine ⟨h.1.keep hp ps c' (by decide) fr (by ofs), h.2, heax, fun hy => ?_, fun hn => ?_⟩
    · rw [hy] at heax; simp only [↓reduceIte] at heax
      exact ⟨hred heax, ball_val hout heax (F.ballMax _ _ hy)⟩
    · rw [hn] at heax
      rcases hout with ⟨h1, _⟩ | ⟨_, h0⟩
      · rw [heax] at h1; cases h1
      · simpa using h0

/-- Whether `SampleInBall` succeeded, in a run that reaches iteration `t`. -/
def ballB (p : Params) (F : PrimsOk P) (t : Nat) (s₀ : State) : Bool :=
  decide (Run p F t s₀) && F.ballF p.τ (CTv p s₀ (p.ℓ * t))

theorem ballB_eq {F : PrimsOk P} {t : Nat} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') :
    ballB p F t s₀ = ballB p F t s₀' := by
  unfold ballB
  by_cases h : Run p F t s₀
  · rw [decide_eq_true h, decide_eq_true ((run_iff ps hq).mp h), (run_at ps hq h).1]
  · rw [decide_eq_false h, decide_eq_false fun h' => h ((run_iff ps hq).mpr h'), Bool.false_and, Bool.false_and]

theorem ballB_of {F : PrimsOk P} {t : Nat} {s₀ : State} (h : Run p F t s₀) :
    ballB p F t s₀ = F.ballF p.τ (CTv p s₀ (p.ℓ * t)) := by
  simp only [ballB, decide_eq_true h, Bool.true_and]

/-- `ZF ← eax = 0`, after `SampleInBall`. -/
theorem ballTest_piece (F : PrimsOk P) (t : Nat) :
    SP p (IB p F t) (fun s₀ s => ∃ s', IB p F t s₀ s' ∧ Ctx (Y p) s₀ s ∧ s.mem = s'.mem ∧
      s.zf = some (!ballB p F t s₀)) (.block [.alu .test .eax (.reg .eax)]) := by
  refine blk_piece (fun _ _ _ h => h.cc.cw.cm.it.kd.ctx) (fun s₀ s hp h => wp_test fun s₁ o₁ z₁ =>
    WP.block_nil_iff.mpr ⟨s, h, h.cc.cw.cm.it.kd.ctx.only o₁ (by simp) (by simp), o₁.mem, ?_⟩) rfl
  rw [z₁, h.eax, ballB_of h.run]
  cases F.ballF p.τ (CTv p s₀ (p.ℓ * t)) <;> rfl

/-! ## The start of the checks -/

/-- `y`, with `z` in place of its first `r` polynomials. -/
abbrev zY (p : Params) (t r : Nat) (s₀ : State) (j : Nat) : Poly :=
  if j < r then Zv p s₀ (p.ℓ * t) j else Yv p s₀ (p.ℓ * t) j

/-- `w`, with `w - cs₂` in place of its first `i` polynomials. -/
abbrev rW (p : Params) (t i : Nat) (s₀ : State) (j : Nat) : Poly :=
  if j < i then W'v p s₀ (p.ℓ * t) j else Wv p s₀ (p.ℓ * t) j

/-- `w - cs₂`, with `w - cs₂ + ct₀` in place of its first `i` polynomials. -/
abbrev hW (p : Params) (t i : Nat) (s₀ : State) (j : Nat) : Poly :=
  if j < i then W''v p s₀ (p.ℓ * t) j else W'v p s₀ (p.ℓ * t) j

/-- What the checks start from. -/
structure KP (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  cc : CC p t s₀ s
  run : Run p F t s₀
  ball : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true

theorem CC.ofMem {t : Nat} {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CC p t s₀ s')
    (c : Ctx (Y p) s₀ s) (hm : s.mem = s'.mem) : CC p t s₀ s :=
  h.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- `ĉ = NTT(c)`, `OK ← 1` and `ONES ← 0`. -/
theorem checksHead_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => KP p F t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (toRq (Cv p s₀ (p.ℓ * t))))
      (CS p t (zY p t 0) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0 (fun _ => true) (fun _ => 0))
      (.seq (nttAt P cP) (.block (st32 oOK 1 ++ st32 oONES 0))) := by
  refine Piece.seq (B := fun s₀ s => CC p t s₀ s ∧ PolyIs s.mem (Buf.addr s₀ cP) (chF (Cv p s₀ (p.ℓ * t))))
    (inPlace_piece (t := ntt) F.ntt (F.ok _ (by simp)) cP rfl (by ofs) (fun _ _ _ h => ⟨h.1.cc.cw.cm.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.cc.keep hp ps c' (by decide) fr (by ofs), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine blk_piece (fun _ _ _ h => h.1.cw.cm.it.kd.ctx) (fun s₀ s hp h => ?_) rfl
  refine wp_st32 hp h.1.cw.cm.it.kd.ctx (sc_ok ps (by decide) (by decide)) 1 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oONES 0)]
  refine wp_st32 hp c₁ (sc_ok ps (by decide) (by decide)) 0 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  have g₁ := (h.1.keep hp ps c₁ (N := 80) (by decide) (fr0 hp (by decide) f₁) (by ofs))
  have g₂ := (g₁.keep hp ps c₂ (N := 80) (by decide) (fr0 hp (by decide) f₂) (by ofs))
  have hc := keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) f₁) (j := 0) (by simp only [nS]; omega) (by ofs) h.2
  have hc' := keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) f₂) (j := 0) (by simp only [nS]; omega) (by ofs) hc
  refine ⟨g₂.cw.cm.it, g₂.ct, hc', g₂.cw.cm.fy.congr fun j hj => by simp, g₂.cw.fw, fun j hj => absurd hj (Nat.not_lt_zero _),
    ?_, v₂, Nat.zero_le _⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) f₂) (sc_ok' ps (by decide) (by decide)) (by ofs)]
  exact v₁

end VG.Proof.MlDsa.X86.Sign
