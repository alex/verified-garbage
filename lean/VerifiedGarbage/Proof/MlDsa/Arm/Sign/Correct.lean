import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseO

/-!
# ML-DSA signing on ARMv7: correctness

The function returns 1 with `Sign_internal`'s signature (within `maxBounds`)
in `sig`, or 0 when `Sign_internal` returns nothing within `minBounds`
(`sign_correct`): its `ExpandA` or its loop does not finish (`signMu_min_A`,
`signMu_min_L`), or an iteration passes (`signMu_max`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : seedE p σ (p.ℓ * i + j) = aSeed (rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2]

theorem ij_lt {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome) :
    expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)) :=
  expandA_some fun i hi j hj => by rw [← seedE_ij hj]; exact hok _ (ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedE p σ e) = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
  exact signMu_none_A (expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)))
    (hL : loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  cases e : expandA p minBounds (rhoOf p σ) with
  | none => exact signMu_none_A e
  | some A' =>
    have := expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ))) {t : Nat}
    (ht : t < 814) (hr : RejT p σ t) (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome)
    (hpass : PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (sigV p σ (p.ℓ * t)) :=
  signMu_some hA (signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega) (iter_pass hp hs hpass))

end

/-! ## After the loop -/

/-- Before the return: `r11`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (D : Nat) (σ s : State) : Prop where
  st : St p D σ s
  r01 : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1
  ok : s.gpr .r11 = 1 →
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (bytesAt s.mem (pa s (.r8, 0)) p.sigLen)
  bad : s.gpr .r11 = 0 → signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none

/-- What the function needs of the layout, besides its pieces. -/
def fChk (p : Params) : Bool :=
  stChk p [] && famChk (sgB p) [] (aBase p) (p.k * p.ℓ) && ikChk p [] && famChk (sgB p) [] (yBase p) p.ℓ &&
    famChk (sgB p) [] 5 p.k && keepB (sgB p) [] (sc oCT) (cLen p) &&
    inB (sgB p) (sc oSV) 36 &&
    decide (scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32)

theorem fChk_ok {p : Params} (h : Ok3 p) : fChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Every check of the layout. -/
def allChk (p : Params) : Bool :=
  aChk p && dChk p && cChk p && bChk p && ksChk p && lChk p && oChk p && fChk p

theorem allChk_ok {p : Params} (h : Ok3 p) : allChk p = true := by
  simp only [allChk, aChk_ok h, dChk_ok h, cChk_ok h, bChk_ok h, ksChk_ok h, lChk_ok h, oChk_ok h, fChk_ok h,
    Bool.and_self]

theorem r11_one {s : State} (h : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1) (hne : s.gpr .r11 ≠ 0) : s.gpr .r11 = 1 := by
  rcases h with e | e
  · exact absurd e hne
  · exact e

theorem rest_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) {σ s : State} (h : IM p D σ s) :
    WP isa (rest P p) s (FS p D σ) := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, ik⟩, fy⟩, f5⟩, kct⟩, -⟩, -⟩ := hf'
  have hp := paramsOk h3
  have hA := expandA_max h.ok
  unfold rest
  refine WP.seq (WP.mono (decode_ok hP hd h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (signLoop_ok hP hp hc1 hb hks hl h1) fun s2 h2 => ?_)
  have L2 := h2.k.d.im.st.lay
  unfold ifOk
  refine ifOkElse_ok (D := D) (fun s3 hP3 hcs3 hm3 hne => ?_) fun s3 hP3 hcs3 hm3 he => ?_
  · have h15 := r11_one h2.r01 hne
    obtain ⟨t, ht, hr, hs, hpass, hct, hz, hh⟩ := h2.pass h15
    refine WP.mono (output_ok hP ho (h2.k.step hP3 ik) (by rw [L2.keepBytes hP3 kct, hct])
      (Fam.keep L2 hP3 fy hz) (HFam.keep L2 hP3 f5 hh) hpass (by rw [hcs3 _ (by decide) (by decide), h15]))
      fun s4 ⟨k4, hb4, h154⟩ => ⟨k4.d.im.st, .inr h154, fun _ => by rw [hb4]; exact signMu_max hp hA ht hr hs hpass,
        fun h0 => absurd (h0.symm.trans h154) (by decide)⟩
  · have h15 := he
    have e15 : s3.gpr .r11 = 0 := by rw [hcs3 _ (by decide) (by decide), h15]
    exact WP.block_nil ⟨(h2.k.step hP3 ik).d.im.st, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
      fun _ => signMu_min_L hA (h2.fail h15)⟩

/-! ## The function -/

theorem entry_bytes {σ s : State} {r : Reg} {len : Nat} {R : Region} (hf : Frame [R] σ.mem s.mem)
    (hd : Region.Disjoint ⟨State.addr (σ.gpr r), len⟩ R) (hl : len ≤ 2 ^ 64) {b : Reg} (hb : s.gpr b = σ.gpr r) :
    bytesAt s.mem (pa s (b, 0)) len = bytesAt σ.mem (State.addr (σ.gpr r)) len := by
  rw [pa, hb, BitVec.add_zero]
  exact VG.Proof.MlKem.bytesAt_frame hf (fun R' hR => by rw [List.mem_singleton] at hR; subst hR; exact hd) hl

theorem entry_st {p : Params} {D : Nat} (h3 : Ok3 p) {σ s : State}
    (hpre : (signK p D).pre σ) (ht : Top σ s) (hf : Frame [⟨State.addr (stackArg σ 0), scrLen p⟩] σ.mem s.mem) :
    St p D σ s := by
  have hc := fChk_ok h3
  simp only [fChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hsz := hc.2
  have hpre' := hpre
  obtain ⟨_, _, -, d2, -, d4, -, d6, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hpre'
  exact ⟨ht, sgLay hpre hsz ht,
    entry_bytes hf d2 (by omega) (ht.regs .r4 (by decide)),
    entry_bytes hf d4 (by omega) (ht.regs .r5 (by decide)),
    entry_bytes hf d6 (by omega) (ht.regs .r6 (by decide))⟩

theorem sign_correct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) (σ : State)
    (hpre : (signK p D).pre σ) :
    ∃ t s', Exec isa (Impl.MlDsa.Arm.Sign.sign P p) σ t s' ∧ abiPreserved σ s' ∧ (signK p D).post σ s' := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, hsv⟩, hsz⟩ := hf'
  have main : WP isa (Impl.MlDsa.Arm.Sign.sign P p) σ fun s₅ => (∀ r ∈ preserved, s₅.gpr r = σ.gpr r) ∧
      s₅.sp = σ.sp ∧ ∃ s₄, FS p D σ s₄ ∧ s₅.gpr .r0 = s₄.gpr .r11 ∧ s₅.mem = s₄.mem := by
    unfold Impl.MlDsa.Arm.Sign.sign
    refine WP.seq (WP.mono (pro_ok hpre) fun s₁ ⟨h₁, hf₁, h15⟩ => ?_)
    have S1 := entry_st h3 hpre h₁ hf₁
    refine WP.seq (WP.mono (expandA_ok hP ha S1 h15) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (rest P p)) s₂ (FS p D σ) from ?_) fun s₄ h₄ => ?_)
    · unfold ifOk
      refine ifOkElse_ok (D := D) (fun s₃ hP₃ hcs₃ hm₃ hne => ?_) fun s₃ hP₃ hcs₃ hm₃ he => ?_
      · have h1 := r11_one h₂.r01 hne
        obtain ⟨ok, fam⟩ := h₂.ok h1
        exact rest_ok hP h3 ⟨h₂.st.step hP₃ st0, ok, Fam.keep h₂.st.lay hP₃ fa0 fam⟩
      · have h0 := he
        have e15 : s₃.gpr .r11 = 0 := by rw [hcs₃ _ (by decide) (by decide), h0]
        exact WP.block_nil ⟨h₂.st.step hP₃ st0, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
          fun _ => signMu_min_A (h₂.bad h0)⟩
    · have hn := h₄.st.lay.nw (.r7, scrLen p) (by simp)
      have hge := scrLen_ge p
      exact WP.mono (topEnd_ok h₄.st.top (h₄.st.lay.iR hsv) (by simp only at hn; omega))
        fun s₅ ⟨hr, hg, hm, hsp⟩ => ⟨hg, hsp.trans h₄.st.top.sp, s₄, h₄, hr, hm⟩
  obtain ⟨t, s', he, hF⟩ := main
  obtain ⟨hg, hsp, s₄, h₄, hr, hm⟩ := hF
  refine ⟨t, s', he, ⟨hg, hsp⟩, ?_⟩
  have e14 : pa s₄ (.r8, 0) = State.addr (σ.gpr .r3) := by
    rw [pa, h₄.st.top.regs .r8 (by decide), BitVec.add_zero]; rfl
  show Outcome _ _ _
  rcases h₄.r01 with h0 | h1
  · exact .inr ⟨by rw [hr, h0], h₄.bad h0⟩
  · exact .inl ⟨by rw [hr, h1], maxBounds, by rw [hm, ← e14]; exact h₄.ok h1⟩

end VG.Proof.MlDsa.Arm.Sign
