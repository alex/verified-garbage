import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseK

/-!
# ML-DSA signing on ARMv7: the rejection sampling loop

An iteration (`iter_ok`) either continues, with the next iteration's head
(`IL`), or ends the loop (`XS`): with `r11 = 1` when it passed, as
`signIteration` does within `maxBounds` after the iterations before were
rejected; with `r11 = 0` when `signLoop` returns nothing within `minBounds`
(its `SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem paramsOk {p : Params} (h : Ok3 p) : ParamsOk p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

section
variable (p : Params) (σ : State)

/-- `signLoop`'s arguments for the function entered in `σ`: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, `μ`, `ρ″`. -/
abbrev loopF (b : Bounds) (n κ : Nat) : Option (List Byte × List Poly × List (Vector Bool Spec.MlDsa.n)) :=
  signLoop p b (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) n κ

abbrev iterF (b : Bounds) (κ : Nat) : Option (List Byte × Option (List Poly × List (Vector Bool Spec.MlDsa.n))) :=
  signIteration p b (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) κ

end

section
variable {p : Params} {σ : State} {κ : Nat}

theorem iterF_eq (hp : ParamsOk p) (b : Bounds) :
    iterF p σ b κ = (sampleInBall p.τ b.ball (CTv p σ κ)).map fun c =>
      (CTv p σ κ, if passF p (Am p σ) (S1v p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c then
        some ((List.range p.ℓ).map (zF p (S1v p σ) (rppOf p σ) κ c),
          (List.range p.k).map (hF p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ c)) else none) :=
  signIteration_eqF hp b _ _ _ _ _ _ κ

theorem cV_eq (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    sampleInBall p.τ maxBounds.ball (CTv p σ κ) = some (cV p σ κ) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  simp only [cV, hc, Option.getD_some]

theorem iter_rej (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome)
    (hf : ¬ PassV p σ κ) : iterF p σ maxBounds κ = some (CTv p σ κ, none) := by
  rw [iterF_eq hp, cV_eq h, Option.map_some, ifn hf]

theorem iter_pass (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome)
    (hf : PassV p σ κ) : iterF p σ maxBounds κ =
      some (CTv p σ κ, some ((List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))) := by
  rw [iterF_eq hp, cV_eq h, Option.map_some, ifp hf]

theorem iter_none (h : sampleInBall p.τ minBounds.ball (CTv p σ κ) = none) : iterF p σ minBounds κ = none := by
  rw [iterF, signIteration_eq, signCommit_eq, h]; rfl

end

/-! ## The end of the loop -/

/-- The loop ended: in `r11`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (D : Nat) (σ : State) (s : State) : Prop where
  k : IK p D σ s
  r01 : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1
  pass : s.gpr .r11 = 1 → ∃ t < 814, RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome ∧ PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t) ∧ Fam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t)) ∧
    HFam s 5 p.k (Hv p σ (p.ℓ * t))
  fail : s.gpr .r11 = 0 → loopF p σ minBounds minBounds.sign 0 = none

/-- `SampleInBall` did not finish within `minBounds`: `r11 = 0`, `CNT = 1`. -/
structure EB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p D σ s
  none : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none
  r11 : s.gpr .r11 = 0
  cnt : s.mem.readW (pa s (sc oCNT)) 32 = 1
  t_lt : t < 814
  rej : RejT p σ t

theorem rej_zero {p : Params} {σ : State} {t : Nat} (h : RejT p σ t) :
    Rej p (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
      ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) maxBounds 0 t := h

theorem loop_none_ball {p : Params} {σ : State} {t : Nat} (h : RejT p σ t)
    (hn : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inr (by rw [Nat.zero_add]; exact iter_none hn))

theorem loop_none_exh {p : Params} {σ : State} (h : RejT p σ 814) : loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inl (by decide))

/-! ## An iteration -/

/-- After iteration `t`: the loop continues with iteration `t + 1`, or ends. -/
def LP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.z = false ∧ IL p D σ (t + 1) s) ∨ (s.z = true ∧ XS p D σ s)

/-- What the end of an iteration needs of the layout. -/
def lChk (p : Params) : Bool :=
  inB (sgW p) (sc oCNT) 4 && inB (sgB p) (sc oCNT) 4 && ikChk p [(sc oCNT, 4)] && keepB (sgB p) [(sc oCNT, 4)] (sc oKAP) 4 &&
    keepB (sgB p) [(sc oCNT, 4)] (sc oCT) (cLen p) && famChk (sgB p) [(sc oCNT, 4)] (yBase p) p.ℓ &&
    famChk (sgB p) [(sc oCNT, 4)] 5 p.k && icwChk p [] p.k && keepB (sgB p) [] (sc oCT) (cLen p) &&
    keepB (sgB p) [] cP 1024 && ikChk p [] &&
    keepB (sgB p) [(sc oKAP, 4)] (sc oCNT) 4 && inB (sgW p) (sc oKAP) 4 && ikChk p [(sc oKAP, 4)]

theorem lChk_ok {p : Params} (h : Ok3 p) : lChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem ofNat32_sub_one {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 32) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : (1 : BitVec 32).toNat = 1 := rfl
  rw [this]
  omega

theorem ofNat32_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

/-- `CNT ← CNT - 1`, setting Z when it reaches 0. -/
abbrev decCnt : List Instr := [.ldr .r0 .r7 oCNT, .subs .r0 .r0 (.imm 1), .str .r0 .r7 oCNT]

/-- `decW_ok` in the layout. -/
theorem decCnt_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s)
    (w1 : inB wbs (sc oCNT) 4 = true) :
    WP isa (.block decCnt) s fun s' => (s'.mem = s.mem.writeW (pa s (sc oCNT)) (s.mem.readW (pa s (sc oCNT)) 32 - 1) ∧
      s'.z = (s.mem.readW (pa s (sc oCNT)) 32 - 1 == 0)) ∧ PPostB D s s' [(sc oCNT, 4)] ∧ CS s s' := by
  have ac : State.addr (s.gpr .r7 + BitVec.ofNat 32 oCNT) = pa s (sc oCNT) := L.pa32W (p := sc oCNT) w1 (by decide)
  refine WP.mono (decW_ok (sc oCNT) (by decide) (by decide) s (by rw [ac]; exact L.iW w1))
    fun s' ⟨⟨hm, hz⟩, hg, hrd, hwr, hsp⟩ => ?_
  rw [ac] at hm hz
  have hf : Frame [⟨pa s (sc oCNT), 4⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hcs : CS s s' := fun r hr _ => hg r fun h => by
    simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
  exact ⟨⟨hm, hz⟩, PostB.of_cs hcs hrd hwr hsp hf, hcs⟩

theorem dec_end {D : Nat} {p : Params} (hp : ParamsOk p) (hc : lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : EP p D σ t s ∨ EF p D σ t s ∨ EB p D σ t s) :
    WP isa (.block decCnt) s (LP p D σ t) := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, k1⟩, k2⟩, k3⟩, f1⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have hk : IK p D σ s := by rcases h with h | h | h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono (decCnt_okB L w1) fun s' ⟨⟨hm, hz⟩, hP, hcs⟩ => ?_
  have K := hk.step hP k1
  have e15 : s'.gpr .r11 = s.gpr .r11 := hcs _ (by decide) (by decide)
  rcases h with h | h | h
  · -- passed
    rw [h.cnt] at hz
    refine .inr ⟨by rw [hz]; rfl, K, .inr (e15.trans h.r11), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [L.keepBytes hP k3, h.ct], Fam.keep L hP f1 h.z, HFam.keep L hP f2 h.h⟩,
      fun h0 => absurd (h0.symm.trans (e15.trans h.r11)) (by decide)⟩
  · -- rejected
    have hr : RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact iter_rej hp h.some h.fail)
    rw [h.cnt, ofNat32_sub_one (by have := h.t_lt; omega) (by have := h.t_lt; omega),
      ofNat32_beq_zero (by have := h.t_lt; omega)] at hz
    by_cases ht : t = 813
    · subst ht
      refine .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r11),
        fun h1 => absurd (h1.symm.trans (e15.trans h.r11)) (by decide), fun _ => loop_none_exh hr⟩
    · have hne : decide (814 - t - 1 = 0) = false := by have := h.t_lt; simp only [decide_eq_false_iff_not]; omega
      refine .inl ⟨by rw [hz, hne], K, by rw [L.keepW hP k2, h.kap], ?_, by have := h.t_lt; omega, hr⟩
      rw [hP.pa (by decide), hm, Mem.readW_writeW_self32, h.cnt,
        ofNat32_sub_one (by have := h.t_lt; omega) (by have := h.t_lt; omega), Nat.sub_sub]
  · -- `SampleInBall` failed
    rw [h.cnt] at hz
    exact .inr ⟨by rw [hz]; rfl, K, .inl (e15.trans h.r11),
      fun h1 => absurd (h1.symm.trans (e15.trans h.r11)) (by decide), fun _ => loop_none_ball h.rej h.none⟩

theorem cmp0_ok (s : State) : WP isa (.block [.cmp .r0 (.imm 0)]) s fun s₁ =>
    s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp ∧ s₁.z = (s.gpr .r0 == 0) := by
  run_block []
  simp

theorem IB.step0 {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : IB p D σ t s) (hc : lChk p = true)
    (hP : PPostB D s s' []) (hax : s'.gpr .r0 = s.gpr .r0) : IB p D σ t s' := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, c1⟩, c2⟩, c3⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := h.c.l.st.lay
  refine ⟨h.c.step hP c1, by rw [L.keepBytes hP c2, h.ct], hax ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (hax ▸ h0)⟩
  obtain ⟨hc', hs⟩ := h.ok (hax ▸ h1)
  exact ⟨L.keepPoly hP c3 hc', hs⟩

theorem test_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State} (h : IB p D σ t s) :
    WP isa (.block [.cmp .r0 (.imm 0)]) s fun s' =>
      (IB p D σ t s' ∧ s'.z = (s'.gpr .r0 == 0)) ∧ s'.gpr .r0 = s.gpr .r0 := by
  refine WP.mono (cmp0_ok s) fun s3 ⟨g3, hm3, hrd, hwr, hsp, hz3⟩ => ?_
  have hcs : CS s s3 := fun r _ _ => by rw [g3]
  have hP3 : PPostB D s s3 [] := PostB.of_cs hcs hrd hwr hsp (by rw [hm3]; exact Frame.refl _ _)
  have hax3 : s3.gpr .r0 = s.gpr .r0 := by rw [g3]
  exact ⟨⟨h.step0 hc4 hP3 hax3, by rw [hz3, hax3]⟩, hax3⟩

theorem IB.ka {D : Nat} {p : Params} {σ : State} {t : Nat} {s : State} (h : IB p D σ t s)
    (h1 : s.gpr .r0 = 1) : KA p D σ t s :=
  ⟨h.c, h.ct, (h.ok h1).1, (h.ok h1).2⟩

theorem mov0_ok (s : State) : WP isa (.block [.mov .r11 (.imm 0)]) s fun s' => s'.gpr .r11 = 0 ∧ Keep [.r11] s s' := by
  run_block []
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

theorem else_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State} (h : IB p D σ t s)
    (h0 : s.gpr .r0 = 0) :
    WP isa (.block (([.mov .r11 (.imm 0)] : List Instr) ++ setW (sc oCNT) 1)) s (EB p D σ t) := by
  have hc4' := hc4
  simp only [lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, k0⟩, -⟩, -⟩, -⟩ := hc4'
  rw [WP.block_append_iff]
  refine WP.mono (mov0_ok s) fun s4 ⟨h154, k4⟩ => ?_
  have hP4 : PPostB D s s4 [] := (postB11 k4 _).1
  have K4 := h.c.l.k.step hP4 k0
  have L4 := K4.d.im.st.lay
  refine WP.mono (setW_okB L4 (by decide) (by decide) w1) fun s5 ⟨hP5, hcs5, hm5⟩ => ?_
  exact ⟨K4.step hP5 k1, h.bad h0, by rw [hcs5 _ (by decide) (by decide), h154],
    by rw [hP5.pa (by decide), hm5, Mem.readW_writeW_self32]; rfl, h.c.l.t_lt, h.c.l.rej⟩

/-- What the end of an iteration keeps, for the proof that two runs leak the same. -/
theorem decF {D : Nat} {p : Params} (hc : lChk p = true) {σ : State} {s : State} (hk : IK p D σ s) :
    WP isa (.block decCnt) s fun s' =>
      s'.z = (s.mem.readW (pa s (sc oCNT)) 32 - 1 == 0) ∧ s'.gpr .r11 = s.gpr .r11 ∧
      bytesAt s'.mem (pa s' (sc oCT)) (cLen p) = bytesAt s.mem (pa s (sc oCT)) (cLen p) ∧
      ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, -⟩, -⟩, k3⟩, -⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (decCnt_okB L w1) fun s' ⟨⟨_, hz⟩, hP, hcs⟩ => ?_
  exact ⟨hz, hcs _ (by decide) (by decide), L.keepBytes hP k3, fun f h => HFam.keep L hP f2 h⟩

theorem iter_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : cChk p = true)
    (hc2 : bChk p = true) (hc3 : ksChk p = true) (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : IL p D σ t s) : WP isa (iter P p) s (LP p D σ t) := by
  unfold iter
  refine WP.seq (WP.mono (commit_ok hP hc1 h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (ball_ok hP hc2 h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (test_ok hc4 h2) fun s3 ⟨⟨I3, hz3⟩, _⟩ => ?_)
  refine WP.seq (WP.ite (M := isa) (!(s3.gpr .r0 == 0)) (show some (!s3.z) = _ by rw [hz3])
    (fun hb => ?_) fun hb => ?_)
  · have h1 : s3.gpr .r0 = 1 := by
      rcases I3.r01 with e | e
      · rw [e] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (checks_ok hP hc3 (I3.ka h1)) fun s' h' => dec_end hp hc4 (h'.elim .inl (fun h => .inr (.inl h)))
  · exact WP.mono (else_ok hc4 I3 (by simpa using hb)) fun s' h' => dec_end hp hc4 (.inr (.inr h'))

/-! ## The loop -/

theorem loopInit_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {s : State} (h : IK p D σ s) :
    WP isa (.block (setW (sc oKAP) 0 ++ setW (sc oCNT) 814)) s (IL p D σ 0) := by
  have hc4' := hc4
  simp only [lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, kk'⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, wk⟩, ik⟩ := hc4'
  rw [WP.block_append_iff]
  have L := h.d.im.st.lay
  refine WP.mono (setW_okB L (by decide) (by decide) wk) fun s1 ⟨hP1, _, hm1⟩ => ?_
  have K1 := h.step hP1 ik
  refine WP.mono (setW_okB K1.d.im.st.lay (by decide) (by decide) w1) fun s2 ⟨hP2, _, hm2⟩ => ?_
  exact ⟨K1.step hP2 k1, by
      rw [K1.d.im.st.lay.keepW hP2 kk', hP1.pa (by decide), hm1, Mem.readW_writeW_self32]; rfl,
    by rw [hP2.pa (by decide), hm2, Mem.readW_writeW_self32], by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem signLoop_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : cChk p = true)
    (hc2 : bChk p = true) (hc3 : ksChk p = true) (hc4 : lChk p = true) {σ : State} {s : State}
    (h : IK p D σ s) : WP isa (Impl.MlDsa.Arm.Sign.signLoop P p) s (XS p D σ) := by
  unfold Impl.MlDsa.Arm.Sign.signLoop
  refine WP.seq (WP.mono (loopInit_ok hc4 h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ IL p D σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (iter_ok hP hp hc1 hc2 hc3 hc4 hs) fun s' h' => ?_
  have hev : ∀ s : State, isa.eval .ne s = some (!s.z) := fun _ => rfl
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [hev, hz]; rfl, 814 - (t + 1), by have := hs.t_lt; omega, t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [hev, hz]; rfl, hX⟩

end VG.Proof.MlDsa.Arm.Sign
