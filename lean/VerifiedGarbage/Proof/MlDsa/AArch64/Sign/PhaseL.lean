import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK

/-!
# ML-DSA signing on AArch64: the rejection sampling loop

An iteration (`iter_ok`) either continues, with the next iteration's head
(`IL`), or ends the loop (`XS`): with `x24 = 1` when it passed, as
`signIteration` does within `maxBounds` after the iterations before were
rejected; with `x24 = 0` when `signLoop` returns nothing within `minBounds`
(its `SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only Keep wp_movz wp_nil)
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

/-- The loop ended: in `x24`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (D : Nat) (σ : State) (s : State) : Prop where
  k : IK p D σ s
  r01 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1
  pass : s.gpr .x24 = 1 → ∃ t < 814, RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome ∧ PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t) ∧ Fam s (yBase p) p.ℓ (Zv p σ (p.ℓ * t)) ∧
    HFam s 5 p.k (Hv p σ (p.ℓ * t))
  fail : s.gpr .x24 = 0 → loopF p σ minBounds minBounds.sign 0 = none

/-- `SampleInBall` did not finish within `minBounds`: `x24 = 0`, `CNT = 1`. -/
structure EB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p D σ s
  none : sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ * t)) = none
  x24 : s.gpr .x24 = 0
  cnt : s.mem.readW (pa s (sc oCNT)) 64 = 1
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

/-- After iteration `t`: the loop continues with iteration `t + 1` (`x9 ≠ 0`), or ends (`x9 = 0`). -/
def LP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.gpr .x9 ≠ 0 ∧ IL p D σ (t + 1) s) ∨ (s.gpr .x9 = 0 ∧ XS p D σ s)

/-- What the end of an iteration needs of the layout. -/
def lChk (p : Params) : Bool :=
  inB (sgW p) (sc oCNT) 8 && inB (sgB p) (sc oCNT) 8 && ikChk p [(sc oCNT, 8)] && keepB (sgR p) (sgW p) [(sc oCNT, 8)] (sc oKAP) 8 &&
    keepB (sgR p) (sgW p) [(sc oCNT, 8)] (sc oCT) (cLen p) && famChk (sgR p) (sgW p) [(sc oCNT, 8)] (yBase p) p.ℓ &&
    famChk (sgR p) (sgW p) [(sc oCNT, 8)] 5 p.k && icwChk p [] p.k && keepB (sgR p) (sgW p) [] (sc oCT) (cLen p) &&
    keepB (sgR p) (sgW p) [] cP 1024 && ikChk p [] &&
    keepB (sgR p) (sgW p) [(sc oKAP, 8)] (sc oCNT) 8 && inB (sgW p) (sc oKAP) 8 && ikChk p [(sc oKAP, 8)]

theorem lChk_ok {p : Params} (h : Ok3 p) : lChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem one_sub_one : (1 : BitVec 64) - BitVec.ofNat 64 1 = 0 := by decide

theorem dec_end {D : Nat} {p : Params} (hp : ParamsOk p) (hc : lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : EP p D σ t s ∨ EF p D σ t s ∨ EB p D σ t s) : WP isa (.block cntDec) s (LP p D σ t) := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, k1⟩, k2⟩, k3⟩, f1⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have hk : IK p D σ s := by rcases h with h | h | h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono (cntDec_ok s (L.inW w1) (L.inR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ => ?_
  have hf : Frame [⟨pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hP : PPostB D s s' [(sc oCNT, 8)] := postB_of_keep k (by decide) hf
  have K := hk.step hP k1
  have e15 : s'.gpr .x24 = s.gpr .x24 := k.get .x24
  rcases h with h | h | h
  · -- passed
    rw [h.cnt, one_sub_one] at hz
    refine .inr ⟨hz, K, .inr (e15.trans h.x24), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [L.keepBytes hP k3, h.ct], Fam.keep L hP f1 h.z, HFam.keep L hP f2 h.h⟩,
      fun h0 => absurd (h0.symm.trans (e15.trans h.x24)) (by decide)⟩
  · -- rejected
    have hr : RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact iter_rej hp h.some h.fail)
    rw [h.cnt, ofNat_sub_one h.t_lt] at hz
    by_cases ht : t = 813
    · subst ht
      refine .inr ⟨hz, K, .inl (e15.trans h.x24),
        fun h1 => absurd (h1.symm.trans (e15.trans h.x24)) (by decide), fun _ => loop_none_exh hr⟩
    · refine .inl ⟨by
        have hne : (BitVec.ofNat 64 (814 - (t + 1))).toNat ≠ 0 := by
          have := h.t_lt; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        rw [hz]; intro h0; rw [h0] at hne; exact hne rfl, K, by rw [L.keepW hP k2, h.kap], ?_, by have := h.t_lt; omega, hr⟩
      rw [hP.pa (by decide), hm, Mem.readW_writeW_self64, h.cnt, ofNat_sub_one h.t_lt]
  · -- `SampleInBall` failed
    rw [h.cnt, one_sub_one] at hz
    exact .inr ⟨hz, K, .inl (e15.trans h.x24),
      fun h1 => absurd (h1.symm.trans (e15.trans h.x24)) (by decide), fun _ => loop_none_ball h.rej h.none⟩

theorem IB.ka {D : Nat} {p : Params} {σ : State} {t : Nat} {s : State} (h : IB p D σ t s)
    (h1 : (s.gpr .x0).setWidth 32 = 1) : KA p D σ t s :=
  ⟨h.c, h.ct, (h.ok h1).1, (h.ok h1).2⟩

theorem else_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State} (h : IB p D σ t s)
    (h0 : (s.gpr .x0).setWidth 32 = 0) :
    WP isa (.block (([.movz .x .x24 0 0] : List Instr) ++ setQ (sc oCNT) 1)) s (EB p D σ t) := by
  have hc4' := hc4
  simp only [lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, k0⟩, -⟩, -⟩, -⟩ := hc4'
  rw [WP.block_append_iff]
  refine wp_movz fun s4 k4 h154 => wp_nil ?_
  have hP4 : PPostB D s s4 [] := postB24 k4 _
  have K4 := h.c.l.k.step hP4 k0
  have L4 := K4.d.im.st.lay
  refine WP.mono (setQ_ok L4 (by decide) (by decide) w1 (by decide)) fun s5 ⟨hP5, hcs5, hm5⟩ => ?_
  exact ⟨K4.step hP5 k1, h.bad h0, by rw [hcs5.get .x24, h154]; rfl,
    by rw [hP5.pa (by decide), hm5, Mem.readW_writeW_self64]; rfl, h.c.l.t_lt, h.c.l.rej⟩

/-- What the end of an iteration keeps, for the proof that two runs leak the same. -/
theorem decF {D : Nat} {p : Params} (hc : lChk p = true) {σ : State} {s : State} (hk : IK p D σ s) :
    WP isa (.block cntDec) s fun s' =>
      s'.gpr .x9 = s.mem.readW (pa s (sc oCNT)) 64 - BitVec.ofNat 64 1 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s' (sc oCT)) (cLen p) = bytesAt s.mem (pa s (sc oCT)) (cLen p) ∧
      ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, -⟩, -⟩, k3⟩, -⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (cntDec_ok s (L.inW w1) (L.inR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ => ?_
  have hf : Frame [⟨pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hP : PPostB D s s' [(sc oCNT, 8)] := postB_of_keep k (by decide) hf
  exact ⟨hz, k.get .x24, L.keepBytes hP k3, fun f h => HFam.keep L hP f2 h⟩

theorem eval_w0 (s : State) : isa.eval (.nonzero .w .x0) s = some ((s.gpr .x0).setWidth 32 != 0) := rfl

theorem iter_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : cChk p = true)
    (hc2 : bChk p = true) (hc3 : ksChk p = true) (hc4 : lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : IL p D σ t s) : WP isa (iterWith keccak.callee P p) s (LP p D σ t) := by
  unfold iterWith
  refine WP.seq (WP.mono (commit_ok hP hc1 h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (ball_ok hP hc2 h1) fun s3 I3 => ?_)
  refine WP.seq (WP.ite (M := isa) _ (eval_w0 s3) (fun hb => ?_) fun hb => ?_)
  · have h1 : (s3.gpr .x0).setWidth 32 = 1 := by
      rcases I3.r01 with e | e
      · rw [e] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (checks_ok hP hc3 (I3.ka h1)) fun s' h' => dec_end hp hc4 (h'.elim .inl (fun h => .inr (.inl h)))
  · exact WP.mono (else_ok hc4 I3 (by simpa using hb)) fun s' h' => dec_end hp hc4 (.inr (.inr h'))

/-! ## The loop -/

theorem loopInit_ok {D : Nat} {p : Params} (hc4 : lChk p = true) {σ : State} {s : State} (h : IK p D σ s) :
    WP isa (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) s (IL p D σ 0) := by
  have hc4' := hc4
  simp only [lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, kk'⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, wk⟩, ik⟩ := hc4'
  rw [WP.block_append_iff]
  have L := h.d.im.st.lay
  refine WP.mono (setQ_ok L (by decide) (by decide) wk (by decide)) fun s1 ⟨hP1, _, hm1⟩ => ?_
  have K1 := h.step hP1 ik
  refine WP.mono (setQ_ok K1.d.im.st.lay (by decide) (by decide) w1 (by decide)) fun s2 ⟨hP2, _, hm2⟩ => ?_
  exact ⟨K1.step hP2 k1, by
      rw [K1.d.im.st.lay.keepW hP2 kk', hP1.pa (by decide), hm1, Mem.readW_writeW_self64]; rfl,
    by rw [hP2.pa (by decide), hm2, Mem.readW_writeW_self64], by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem eval_x9 (s : State) : isa.eval (.nonzero .x .x9) s = some (s.gpr .x9 != 0) := rfl

theorem signLoop_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : cChk p = true)
    (hc2 : bChk p = true) (hc3 : ksChk p = true) (hc4 : lChk p = true) {σ : State} {s : State}
    (h : IK p D σ s) : WP isa (Impl.MlDsa.AArch64.Sign.signLoopWith keccak.callee P p) s (XS p D σ) := by
  unfold Impl.MlDsa.AArch64.Sign.signLoopWith
  refine WP.seq (WP.mono (loopInit_ok hc4 h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ IL p D σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (iter_ok hP hp hc1 hc2 hc3 hc4 hs) fun s' h' => ?_
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [eval_x9]; simpa using hz, 814 - (t + 1), by have := hs.t_lt; omega, t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [eval_x9, hz]; rfl, hX⟩

end VG.Proof.MlDsa.AArch64.Sign
