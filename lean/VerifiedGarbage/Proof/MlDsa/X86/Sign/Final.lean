import VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseO

/-!
# ML-DSA signing on x86 (32-bit): the body

Untrusted: everything here is checked by Lean. After `ExpandA`, the rest
(`rest_piece`: the private key, the loop, and the signature if the last
iteration passed) leaves `OK`, and `sig` if it is 1, as `Sign_internal`
says (`Outcome`, `rest_outcome`): 1 with the signature within `maxBounds`
if the last iteration passed, and 0 with `Sign_internal` failing within
`minBounds` if `SampleInBall` failed or the 814 iterations were rejected;
and 0 at once if an entry of `Â` failed (`body_piece`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-! ## `Sign_internal` -/

section
variable {s₀ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : seedE p s₀ (p.ℓ * i + j) = aSeed (rhoS p s₀) i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2]

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedE p s₀ e) = none) :
    signMu p minBounds (skOf p s₀) (muOf s₀) (rndOf s₀) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
  exact signMu_none_A (expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoV (skOf p s₀)) = some (amat p (Av (skOf p s₀))))
    (hL : loopV p (skOf p s₀) (muOf s₀) (rndOf s₀) minBounds minBounds.sign 0 = none) :
    signMu p minBounds (skOf p s₀) (muOf s₀) (rndOf s₀) = none := by
  cases e : expandA p minBounds (rhoV (skOf p s₀)) with
  | none => exact signMu_none_A e
  | some A' =>
    have := expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem sigOf_eq (κ : Nat) :
    sigOf p (CTv p s₀ κ, (List.range p.ℓ).map (Zv p s₀ κ), (List.range p.k).map (Hv p s₀ κ)) = sigV p s₀ κ := by
  simp only [sigOf, sigEncode, sigV, zEnc, List.flatMap_map, List.map_map]
  rfl

end

/-! ## The rest -/

/-- After the rest, the last iteration being `NI - 1`. -/
structure RD (p : Params) (F : PrimsOk P) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  run : Run p F (NI p F s₀ - 1) s₀
  ok : scw s₀ s oOK = if (F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) && decide (passS p (NI p F s₀ - 1) s₀))
    then 1 else 0
  sig : F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) = true → passS p (NI p F s₀ - 1) s₀ →
    bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen = sigV p s₀ (p.ℓ * (NI p F s₀ - 1))
  none : F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) = false →
    sampleInBall p.τ minBounds.ball (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) = none

/-- Whether the last iteration passed, in a run whose `Â` was sampled. -/
def lastB (p : Params) (F : PrimsOk P) (s₀ : State) : Bool :=
  decide (Good p F s₀) && F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) &&
    decide (passS p (NI p F s₀ - 1) s₀)

theorem lastB_eq {F : PrimsOk P} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') : lastB p F s₀ = lastB p F s₀' := by
  unfold lastB
  by_cases h : Good p F s₀
  · have h' := (good_iff ps hq).mp h
    have hr : Run p F (NI p F s₀ - 1) s₀ := ⟨h, by have := NI_pos (p := p) F s₀; omega⟩
    obtain ⟨ect, hb⟩ := run_at ps hq hr
    rw [← NI_eq ps hq, ← ect, decide_eq_true h, decide_eq_true h']
    cases e : F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1)))
    · simp only [Bool.true_and, Bool.false_and]
    · simp only [Bool.true_and]
      exact decide_eq_decide.mpr (hb e).1
  · have h' : ¬ Good p F s₀' := fun h' => h ((good_iff ps hq).mpr h')
    rw [decide_eq_false h, decide_eq_false h', Bool.false_and, Bool.false_and, Bool.false_and, Bool.false_and]

/-- The private key, the loop, and the signature if the last iteration passed. -/
theorem rest_piece (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => (∃ s', IA p F.rejF (p.k * p.ℓ) s₀ s' ∧ Ctx (Y p) s₀ s ∧ s.mem = s'.mem) ∧
      okE p F.rejF s₀ (p.k * p.ℓ) = true) (RD p F) (rest P p) := by
  unfold rest
  refine Piece.seq (B := fun s₀ s => KD p s₀ s ∧ Good p F s₀) ((sp_pure (Good p F) (decode_piece F ps)).mono
    (fun s₀ s _ h => ?_) fun _ _ _ h => h) ?_
  · obtain ⟨⟨s', ia, c, m⟩, hg⟩ := h
    exact ⟨⟨c, ⟨by rw [m]; exact ia.fam hg, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩⟩, hg⟩
  refine Piece.seq (signLoop_piece F ps) ?_
  refine okIte_piece (sc_ok' ps (by decide) (by decide)) (lastB p F) (fun s₀ s _ h => ⟨h.ctx, ?_⟩)
    (fun s₀ s₀' _ _ hq => lastB_eq ps hq) ?_ ?_
  · rw [h.ok]; simp only [lastB, decide_eq_true h.run.1, Bool.true_and]
  · let U : State → Nat := fun s₀ => NI p F s₀ - 1
    let φ : State → Prop := fun s₀ => Run p F (U s₀) s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ * U s₀)) = true ∧
      passS p (U s₀) s₀
    refine ((sp_pure φ (output_piece F ps U fun s₀ s₀' _ _ hq => by
      simp only [U, NI_eq ps hq])).mono (fun s₀ s hp h => ?_) fun s₀ s _ h => ?_)
    · obtain ⟨⟨s', fn, c, m⟩, hb⟩ := h
      simp only [lastB, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨_, hs⟩, hq⟩ := hb
      obtain ⟨f1, f2, f3⟩ := fn.out hs hq
      refine ⟨⟨c, by rw [m]; exact f1, by rw [m]; exact f2, fn.run, hs, hq, ?_, by rw [m]; exact f3⟩, fn.run, hs, hq⟩
      rw [scw, m, ← scw, fn.ok, hs, decide_eq_true hq]; rfl
    · obtain ⟨⟨c, ok1, sg⟩, hr, hs, hq⟩ := h
      refine ⟨c, hr, by rw [ok1, hs, decide_eq_true hq]; rfl, fun _ _ => sg, fun e => by rw [hs] at e; cases e⟩
  · refine nil_piece fun s₀ s _ h => ?_
    obtain ⟨⟨s', fn, c, m⟩, hb⟩ := h
    refine ⟨c, fn.run, by rw [scw, m, ← scw]; exact fn.ok, fun hs hq => ?_, fn.none⟩
    simp only [lastB, decide_eq_true fn.run.1, hs, decide_eq_true hq] at hb
    cases hb

end VG.Proof.MlDsa.X86.Sign
