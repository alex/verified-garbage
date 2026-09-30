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

theorem zY_lt {t r j : Nat} {s₀ : State} (h : j < r) : zY p t r s₀ j = Zv p s₀ (p.ℓ * t) j := ifp h _ _
theorem zY_ge {t r j : Nat} {s₀ : State} (h : ¬ j < r) : zY p t r s₀ j = Yv p s₀ (p.ℓ * t) j := ifn h _ _
theorem rW_lt {t i j : Nat} {s₀ : State} (h : j < i) : rW p t i s₀ j = W'v p s₀ (p.ℓ * t) j := ifp h _ _
theorem rW_ge {t i j : Nat} {s₀ : State} (h : ¬ j < i) : rW p t i s₀ j = Wv p s₀ (p.ℓ * t) j := ifn h _ _
theorem hW_lt {t i j : Nat} {s₀ : State} (h : j < i) : hW p t i s₀ j = W''v p s₀ (p.ℓ * t) j := ifp h _ _
theorem hW_ge {t i j : Nat} {s₀ : State} (h : ¬ j < i) : hW p t i s₀ j = W'v p s₀ (p.ℓ * t) j := ifn h _ _

/-- The family whose first `r` values are `g` changed at `r`, for `r + 1`. -/
theorem upd_step {α : Type} {f g : Nat → α} {r j : Nat} (h : j ≠ r) :
    (if j < r + 1 then g j else f j) = if j < r then g j else f j := by
  by_cases e : j < r
  · rw [ifp (by omega : j < r + 1), ifp e]
  · rw [ifn (by omega : ¬ j < r + 1), ifn e]

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

/-! ## Norms -/

/-- `OK ← OK ∧ b`, with `eax = b`. -/
theorem CS.setOK {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (fr : Frame (FR s₀ [sc oOK 4] 0) s.mem s'.mem) (b : State → Bool)
    (v : scw s₀ s' oOK = scw s₀ s oOK &&& s.gpr .eax) (he : s.gpr .eax = if b s₀ then 1 else 0) :
    CS p t fY fW nh (fun s₀ => okb s₀ && b s₀) ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofs),
    h.ct_keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofs),
    keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (j := 0) (by simp only [nS]; omega) (by ofs) h.c,
    h.fy.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, yB]; omega) (by ofs),
    h.fw.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, wB]; omega) (by ofs),
    h.fh.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS]; omega) (by ofs),
    by rw [v, h.ok, he, and01], ?_, h.nh⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) fr) (sc_ok' ps (by decide) (by decide)) (by ofs)]
  exact h.ones

/-- `OK ← OK ∧ ‖f‖∞ < bnd`, for the polynomial `v` in slot `j`, which stays. -/
theorem normAnd_piece (F : PrimsOk P) (ps : PS p) {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool}
    {ones : State → Nat} (j : Nat) (hj : j < nS p) (bnd : Nat) (hb : bnd < 2 ^ 32) (v : State → Poly) :
    SP p (fun s₀ s => CS p t fY fW nh okb ones s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀))
      (fun s₀ s => CS p t fY fW nh (fun s₀ => okb s₀ && decide (normRq [v s₀] < bnd)) ones s₀ s ∧
        PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀)) (normAt P (pS j) bnd) := by
  refine Piece.seq (B := fun s₀ s => (CS p t fY fW nh okb ones s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS j)) (v s₀)) ∧
      s.gpr .eax = if normRq [v s₀] < bnd then 1 else 0)
    (norm_piece F.normLt (F.ok _ (by simp)) bnd hb SC (oP j) (slot_ok' ps hj) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr he => ⟨⟨h.1.keep hp ps c' (by decide) fr (by simp),
        keepP hp ps (by decide) fr hj (by simp) h.2⟩, by rw [he, h.2.2]⟩) ?_
  refine blk_piece (fun _ _ _ h => h.1.1.it.kd.ctx) (fun s₀ s hp h => wp_andOK hp h.1.1.it.kd.ctx ps
    fun s' c' fr v' => ⟨h.1.1.setOK hp ps c' fr (fun s₀ => decide (normRq [v s₀] < bnd)) v' ?_,
      keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) hj (by ofs) h.1.2⟩) rfl
  rw [h.2]; by_cases e : normRq [v s₀] < bnd <;> simp [e]

theorem CS.congr {t nh : Nat} {fY fY' fW fW' : State → Nat → Poly} {okb okb' : State → Bool} {ones : State → Nat}
    {s₀ s : State} (h : CS p t fY fW nh okb ones s₀ s) (e₁ : ∀ j < p.ℓ, fY s₀ j = fY' s₀ j)
    (e₂ : ∀ j < p.k, fW s₀ j = fW' s₀ j) (e₃ : okb s₀ = okb' s₀) : CS p t fY' fW' nh okb' ones s₀ s :=
  { h with fy := h.fy.congr e₁, fw := h.fw.congr e₂, ok := by rw [h.ok, e₃] }

/-- Slot `r` of `y` changed. -/
theorem CS.updY {t nh r : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (hr : r < p.ℓ) (fr : Frame (FR s₀ [pS (yB p + r)] 80) s.mem s'.mem) {fY' : State → Nat → Poly}
    (hv : PolyIs s'.mem (Buf.addr s₀ (pS (yB p + r))) (fY' s₀ r)) (hg : ∀ j < p.ℓ, j ≠ r → fY' s₀ j = fY s₀ j) :
    CS p t fY' fW nh okb ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (by decide) fr (by ofs), h.ct_keep hp ps (by decide) fr (by ofs),
    keepP hp ps (by decide) fr (j := 0) (by simp only [nS]; omega) (by ofs) h.c,
    h.fy.upd hp ps (by decide) fr (by simp only [nS, yB]; omega) hr (by ofs) hv hg,
    h.fw.keep hp ps (by decide) fr (by simp only [nS, wB]; omega) (by ofs),
    h.fh.keep hp ps (by decide) fr (by simp only [nS]; omega) (by ofs),
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ok,
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ones, h.nh⟩

/-- Slot `i` of `w` changed. -/
theorem CS.updW {t nh i : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (hi : i < p.k) (fr : Frame (FR s₀ [pS (wB p + i)] 80) s.mem s'.mem) {fW' : State → Nat → Poly}
    (hv : PolyIs s'.mem (Buf.addr s₀ (pS (wB p + i))) (fW' s₀ i)) (hg : ∀ j < p.k, j ≠ i → fW' s₀ j = fW s₀ j) :
    CS p t fY fW' nh okb ones s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (by decide) fr (by ofs), h.ct_keep hp ps (by decide) fr (by ofs),
    keepP hp ps (by decide) fr (j := 0) (by simp only [nS]; omega) (by ofs) h.c,
    h.fy.keep hp ps (by decide) fr (by simp only [nS, yB]; omega) (by ofs),
    h.fw.upd hp ps (by decide) fr (by simp only [nS, wB]; omega) hi (by ofs) hv hg,
    h.fh.keep hp ps (by decide) fr (by simp only [nS]; omega) (by ofs),
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ok,
    by rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ones, h.nh⟩

/-! ## `z` -/

/-- `z[r] = y[r] + NTT⁻¹(ĉ ŝ₁[r])` in place of `y[r]`, and its norm. -/
theorem zR_piece (F : PrimsOk P) (ps : PS p) (t r : Nat) (hr : r < p.ℓ) :
    SP p (CS p t (zY p t r) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0))
      (CS p t (zY p t (r + 1)) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) (r + 1)) (fun _ => 0))
      (zR P p r) := by
  have hj : s1B p + r < nS p := by simp only [nS, s1B]; omega
  have hy : yB p + r < nS p := by simp only [nS, yB]; omega
  have hβ := ps.hβ
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t r) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S1 p s₀ r)))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP 1) SC (oP 0) SC (oP (s1B p + r)) (by ofs)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (fam_at h.it.kd.dk.f1 hr).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofs), by
        rw [h.c.2, (fam_at h.it.kd.dk.f1 hr).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t r) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (nttInv (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S1 p s₀ r))))
    (inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) t1P rfl (by ofs) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofs), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := CS p t (zY p t (r + 1)) (fun s₀ => Wv p s₀ (p.ℓ * t)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) r) (fun _ => 0))
    (acc_piece (op := add) F.add (F.ok _ (by simp)) SC (oP (yB p + r)) SC (oP 1) (by ofs)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, (fam_at h.1.fy hr).1, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => h.1.updY hp ps c' hr fr (by
        rw [(fam_at h.1.fy hr).2, h.2.2, zY_ge (Nat.lt_irrefl r)] at hq
        rw [zY_lt (Nat.lt_succ_self r)]; exact hq) fun j _ hjr => upd_step hjr) ?_
  refine (normAnd_piece F ps (yB p + r) hy (p.γ₁ - p.β) (by omega) (fun s₀ => Zv p s₀ (p.ℓ * t) r)).mono
    (fun s₀ s _ h => ⟨h, by have := fam_at h.fy hr; rwa [zY_lt (Nat.lt_succ_self r)] at this⟩)
    fun s₀ s _ h => h.1.congr (fun _ _ => rfl)
      (fun _ _ => rfl) (by simp only [okZ, all_range_succ])

/-! ## `r₀` -/

/-- `w[i] - NTT⁻¹(ĉ ŝ₂[i])` in place of `w[i]`, and the norm of its `LowBits`. -/
theorem r0R_piece (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CS p t (zY p t p.ℓ) (rW p t i) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0))
      (CS p t (zY p t p.ℓ) (rW p t (i + 1)) 0 (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) (i + 1))
        (fun _ => 0)) (r0R P p i) := by
  have hj : s2B p + i < nS p := by simp only [nS, s2B]; omega
  have hβ := ps.hβ
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (rW p t i) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S2 p s₀ i)))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP 1) SC (oP 0) SC (oP (s2B p + i)) (by ofs)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (fam_at h.it.kd.dk.f2 hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofs), by
        rw [h.c.2, (fam_at h.it.kd.dk.f2 hi).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (rW p t i) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t1P) (nttInv (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (S2 p s₀ i))))
    (inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) t1P rfl (by ofs) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofs), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := CS p t (zY p t p.ℓ) (rW p t (i + 1)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0))
    (acc_piece (op := sub) F.sub (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP 1) (by ofs)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, (fam_at h.1.fw hi).1, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => h.1.updW hp ps c' hi fr (by
        rw [(fam_at h.1.fw hi).2, h.2.2, rW_ge (Nat.lt_irrefl i)] at hq
        rw [rW_lt (Nat.lt_succ_self i)]; exact hq) fun j _ hji => upd_step hji) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (rW p t (i + 1)) 0
      (fun s₀ => okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) i) (fun _ => 0) s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t2P) (R0v p s₀ (p.ℓ * t) i))
    (lb_piece F.lowBits (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (oP (wB p + i)) SC (oP 2) (by ofs)
      (fun _ _ _ h => ⟨h.it.kd.ctx, (fam_at h.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofs), by
        rw [(fam_at h.fw hi).2, rW_lt (Nat.lt_succ_self i)] at hq; exact hq⟩) ?_
  refine (normAnd_piece F ps 2 (by simp only [nS]; omega) (p.γ₂ - p.β) (by omega) (fun s₀ => R0v p s₀ (p.ℓ * t) i)).mono
    (fun s₀ s _ h => h) fun s₀ s _ h => h.1.congr (fun _ _ => rfl) (fun _ _ => rfl)
      (by simp only [okR, all_range_succ, Bool.and_assoc])

/-! ## `ct₀` and the hint -/

theorem zq_sub_add (a b : Zq) : a - (a + b) = -b := by
  apply Fin.ext
  have ha := a.isLt; have hb := b.isLt
  simp only [Fin.sub_def, Fin.add_def, Fin.neg_def, q] at *
  omega

theorem sub_add_neg (a b : Poly) : sub a (add a b) = neg b := by
  apply Vector.ext
  intro j hj
  simp only [sub, add, neg, Vector.getElem_zipWith, Vector.getElem_map, zq_sub_add]

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by rw [Vector.length_toList])

theorem sum_range_succ (f : Nat → Nat) (i : Nat) :
    ((List.range (i + 1)).map f).sum = ((List.range i).map f).sum + f i := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]

theorem onesS_succ {s₀ : State} {κ i : Nat} : onesS p s₀ κ (i + 1) = onesS p s₀ κ i + hintOnes [Hv p s₀ κ i] :=
  sum_range_succ _ i

theorem onesS_le {s₀ : State} {κ : Nat} : ∀ i, onesS p s₀ κ i ≤ 256 * i
  | 0 => by simp [onesS]
  | i + 1 => by rw [onesS_succ]; have := onesS_le (s₀ := s₀) (κ := κ) i; have := hintOnes_le (Hv p s₀ κ i); omega

/-- `ONES ← ONES + eax`, with `eax` the number of 1s of the hint's polynomial `nh - 1`. -/
theorem CS.addOnes {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (fr : Frame (FR s₀ [sc oONES 4] 0) s.mem s'.mem) {x : State → Nat}
    (v : scw s₀ s' oONES = scw s₀ s oONES + s.gpr .eax) (he : (s.gpr .eax).toNat = x s₀)
    (hb : ones s₀ + x s₀ < 2 ^ 32) : CS p t fY fW nh okb (fun s₀ => ones s₀ + x s₀) s₀ s' := by
  have := h.nh
  refine ⟨h.it.keep hp ps c' (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofs),
    h.ct_keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by ofs),
    keepP hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (j := 0) (by simp only [nS]; omega) (by ofs) h.c,
    h.fy.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, yB]; omega) (by ofs),
    h.fw.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS, wB]; omega) (by ofs),
    h.fh.keep hp ps (N := 80) (by decide) (fr0 hp (by decide) fr) (by simp only [nS]; omega) (by ofs), ?_, ?_, h.nh⟩
  · rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) fr) (sc_ok' ps (by decide) (by decide)) (by ofs)]
    exact h.ok
  · rw [v, h.ones]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, he, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := ones s₀) (by omega),
      Nat.mod_eq_of_lt hb]

/-- The hint's polynomial `nh`, made. -/
theorem CS.addHint {t nh : Nat} {fY fW : State → Nat → Poly} {okb : State → Bool} {ones : State → Nat}
    {s₀ s s' : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : CS p t fY fW nh okb ones s₀ s) (c' : Ctx (Y p) s₀ s')
    (hn : nh < p.k) (fr : Frame (FR s₀ [pS (5 + nh)] 80) s.mem s'.mem)
    (hh : HintIs s'.mem (Buf.addr s₀ (pS (5 + nh))) 1 [Hv p s₀ (p.ℓ * t) nh]) :
    CS p t fY fW (nh + 1) okb ones s₀ s' :=
  have k := h.keep hp ps c' (by decide) fr (by ofs)
  { k with fh := k.fh.snoc hh, nh := hn }

/-- The okays of the checks of `ct₀` so far. -/
abbrev okH (p : Params) (t i : Nat) (s₀ : State) : Bool :=
  okZ p s₀ (p.ℓ * t) p.ℓ && okR p s₀ (p.ℓ * t) p.k && okT p s₀ (p.ℓ * t) i

/-- `ct₀[i]` and its norm, `w - cs₂ + ct₀` in place of `w[i]`, and `h[i]`. -/
theorem hR_piece (F : PrimsOk P) (ps : PS p) (t i : Nat) (hi : i < p.k) :
    SP p (CS p t (zY p t p.ℓ) (hW p t i) i (okH p t i) (fun s₀ => onesS p s₀ (p.ℓ * t) i))
      (CS p t (zY p t p.ℓ) (hW p t (i + 1)) (i + 1) (okH p t (i + 1)) (fun s₀ => onesS p s₀ (p.ℓ * t) (i + 1)))
      (hR P p i) := by
  have hj : t0B p + i < nS p := by simp only [nS, t0B]; omega
  have hwj : wB p + i < nS p := by simp only [nS, wB]; omega
  have hk := ps.hk
  have hβ := ps.hβ
  let H0 : State → State → Prop := CS p t (zY p t p.ℓ) (hW p t i) i (okH p t i) (fun s₀ => onesS p s₀ (p.ℓ * t) i)
  let H1 : State → State → Prop := CS p t (zY p t p.ℓ) (hW p t i) i
    (fun s₀ => okH p t i s₀ && decide (normRq [CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => onesS p s₀ (p.ℓ * t) i)
  let H2 : State → State → Prop := CS p t (zY p t p.ℓ) (hW p t (i + 1)) i
    (fun s₀ => okH p t i s₀ && decide (normRq [CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => onesS p s₀ (p.ℓ * t) i)
  refine Piece.seq (B := fun s₀ s => H0 s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ t3P) (multiplyNTT (chF (Cv p s₀ (p.ℓ * t))) (T0 p s₀ i)))
    (mul_piece F.mul (F.ok _ (by simp)) SC (oP 3) SC (oP 0) SC (oP (t0B p + i)) (by ofs)
      (fun _ _ _ h => ⟨h.it.kd.ctx, h.c.1, (fam_at h.it.kd.dk.f0 hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.keep hp ps c' (by decide) fr (by ofs), by
        rw [h.c.2, (fam_at h.it.kd.dk.f0 hi).2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => H0 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (CT0v p s₀ (p.ℓ * t) i))
    (inPlace_piece (t := nttInv) F.invNtt (F.ok _ (by simp)) t3P rfl (by ofs) (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofs), by rw [h.2.2] at hq; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => H1 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (CT0v p s₀ (p.ℓ * t) i))
    (normAnd_piece F ps 3 (by simp only [nS]; omega) p.γ₂ (by omega) (fun s₀ => CT0v p s₀ (p.ℓ * t) i)) ?_
  refine Piece.seq (B := fun s₀ s => (H1 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (pS 3)) (CT0v p s₀ (p.ℓ * t) i)) ∧
      PolyIs s.mem (Buf.addr s₀ t4P) (W'v p s₀ (p.ℓ * t) i))
    (copy_piece SC (oP (wB p + i)) SC (oP 4) 256 (by decide) (by decide) (by ofs) (fun _ _ _ h => h.1.it.kd.ctx)
      fun s₀ s s' hp h c' fr hb => by
        have fr' : Frame (FR s₀ [t4P] 80) s.mem s'.mem := fr.mono (by simp)
        have hw := fam_at h.1.fw hi
        rw [hW_ge (Nat.lt_irrefl i)] at hw
        exact ⟨⟨h.1.keep hp ps c' (by decide) fr' (by ofs), keepP hp ps (by decide) fr' (by simp only [nS]; omega)
          (by ofs) h.2⟩, polyIs_of_bytes hb hw⟩) ?_
  refine Piece.seq (B := fun s₀ s => H2 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ t4P) (W'v p s₀ (p.ℓ * t) i))
    (acc_piece (op := add) F.add (F.ok _ (by simp)) SC (oP (wB p + i)) SC (oP 3) (by ofs)
      (fun _ _ _ h => ⟨h.1.1.it.kd.ctx, (fam_at h.1.1.fw hi).1, h.1.2.1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.1.updW hp ps c' hi fr (by
        rw [(fam_at h.1.1.fw hi).2, h.1.2.2, hW_ge (Nat.lt_irrefl i)] at hq
        rw [hW_lt (Nat.lt_succ_self i)]; exact hq) fun j _ hji => upd_step hji,
        keepP hp ps (by decide) fr (by simp only [nS]; omega) (by ofs) h.2⟩) ?_
  refine Piece.seq (B := fun s₀ s => H2 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ t4P) (neg (CT0v p s₀ (p.ℓ * t) i)))
    (acc_piece (op := sub) F.sub (F.ok _ (by simp)) SC (oP 4) SC (oP (wB p + i)) (by ofs)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1, (fam_at h.1.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hq => ⟨h.1.keep hp ps c' (by decide) fr (by ofs), by
        rw [h.2.2, (fam_at h.1.fw hi).2, hW_lt (Nat.lt_succ_self i)] at hq
        rw [← sub_add_neg]; exact hq⟩) ?_
  refine Piece.seq (B := fun s₀ s => CS p t (zY p t p.ℓ) (hW p t (i + 1)) (i + 1)
      (fun s₀ => okH p t i s₀ && decide (normRq [CT0v p s₀ (p.ℓ * t) i] < p.γ₂)) (fun s₀ => onesS p s₀ (p.ℓ * t) i) s₀ s ∧
      (s.gpr .eax).toNat = hintOnes [Hv p s₀ (p.ℓ * t) i])
    (hint_piece F.makeHint (F.ok _ (by simp)) p.γ₂ ps.hγ₂ SC (oP 4) SC (oP (wB p + i)) SC (oP (5 + i)) (by ofs)
      (fun _ _ _ h => ⟨h.1.it.kd.ctx, h.2.1, (fam_at h.1.fw hi).1⟩)
      fun s₀ s s' hp h c' fr hh he => by
        rw [h.2.2, (fam_at h.1.fw hi).2, hW_lt (Nat.lt_succ_self i)] at hh he
        exact ⟨h.1.addHint hp ps c' hi fr hh, he⟩) ?_
  refine blk_piece (fun _ _ _ h => h.1.it.kd.ctx) (fun s₀ s hp h => wp_addOnes hp h.1.it.kd.ctx ps
    fun s' c' fr v => ?_) rfl
  have hb : onesS p s₀ (p.ℓ * t) i + hintOnes [Hv p s₀ (p.ℓ * t) i] < 2 ^ 32 := by
    have := onesS_le (p := p) (s₀ := s₀) (κ := p.ℓ * t) i; have := hintOnes_le (Hv p s₀ (p.ℓ * t) i); omega
  have k := (h.1.addOnes hp ps c' fr (x := fun s₀ => hintOnes [Hv p s₀ (p.ℓ * t) i]) v h.2 hb).congr
    (fun _ _ => rfl) (fun _ _ => rfl) (okb' := okH p t (i + 1)) (by simp only [okH, okT, all_range_succ, Bool.and_assoc])
  exact { k with ones := by rw [k.ones, onesS_succ] }

end VG.Proof.MlDsa.X86.Sign
