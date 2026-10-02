import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.StageC
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Instrs
import VerifiedGarbage.Proof.MlDsa.Verify.Norm

/-!
# ML-DSA verification on x86-64: correctness

Untrusted: everything here is checked by Lean. `vg_mldsa*_verify` returns 1
only if `verifyMu` accepts the signature for some bounds on the samplers'
loops, and 0 only if it does not accept it with the least bounds
(`verify_correct`): a malformed hint returns 0 at once, a `z` too large
after the norms, and otherwise `r15` holds the result of the samplers
(`S4`) and then the comparison of `c̃` (`compute_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (vPk p σ) (vMu σ) (vSig p σ)

/-- At the end, before the epilogue: the result in `r15`. -/
def Fin (p : Params) (σ s : State) : Prop :=
  T p σ s ∧ ((s.gpr .r15 = flag True ∧ ∃ b, vv p σ b = some true) ∨
    (s.gpr .r15 = flag False ∧ vv p σ minBounds ≠ some true))

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : vv p σ b = some false) : vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := verifyMu_mono (bmax_left b minBounds).rejNTT (bmax_left b minBounds).ball h
    have e₂ := verifyMu_mono (bmax_right b minBounds).rejNTT (bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

/-- The facts about the parameters the proof needs. -/
theorem parChk : ∀ p ∈ params, p.γ₁ ∈ gamma1s ∧ 0 < p.γ₁ - p.β ∧ keepB (vB p) [] (pH 0) (1024 * p.k) = true ∧
    ∀ i < p.ℓ, keepB (vB p) [] (pZ i) 1024 = true := by decide

theorem S2.flag {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ) {h : List (Vector Bool n)} {j : Nat}
    (hj : j ≤ p.ℓ) {s s' : State} (hs : S2 p h j σ s) (hP : PPostB s s' []) (e : s'.gpr .r15 = s.gpr .r15) :
    S2 p h j σ s' := by
  have L := hs.t.lay hp hv
  obtain ⟨_, _, kh, kz⟩ := parChk p hp
  exact ⟨hs.t.step hp hv hP (tChk_nil p hp), L.keepHint hP kh hs.hint,
    fun i hi => L.keepPoly hP (kz i (by omega)) (hs.z i hi), by rw [e]; exact hs.r15⟩

theorem S4.toSC {p : Params} {h : List (Vector Bool n)} {σ s : State} (hs : S4 p h σ s) {q : Bool}
    (h15 : s.gpr .r15 = flag (q = true)) :
    SC p h (fun r c => polyAt s.mem (pa s (pA p.ℓ r c))) (q = true) 0 (polyAt s.mem (pa s pC)) 0 σ s :=
  ⟨hs.t, hs.hint, fun r hr c hc => ⟨hs.red r hr c hc, rfl⟩,
    fun i hi => by rw [iteN (Nat.not_lt_zero _)]; exact hs.z i hi, ⟨hs.redC, rfl⟩,
    fun _ h => absurd h (Nat.not_lt_zero _), h15⟩

/-- After the norms: the samplers, the rows, the hash and the comparison. -/
theorem cs_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} (hh : vHint p (vSig p σ) = some h)
    (hn : ∀ i < p.ℓ, normRq [toRq (vZ p (vSig p σ) i)] < p.γ₁ - p.β) {s : State} (hs : S4 p h σ s) :
    WP isa (compute P p) s (Fin p σ) := by
  obtain ⟨q, h15, hok, hbad⟩ := hs.ok
  have hSC := hs.toSC h15
  refine WP.mono (compute_ok C hp hv hSC) fun s' ⟨ht, h15'⟩ => ⟨ht, ?_⟩
  cases q with
  | false =>
    refine .inr ⟨by rw [h15']; exact flag_congr (by simp), ?_⟩
    rcases hbad rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_rej_none minBounds _ _ hh hr hc hn']; nofun
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_ball_none minBounds _ _ hh (Option.map_eq_none_iff.mp hn')]; nofun
  | true =>
    obtain ⟨hA, hB⟩ := hok rfl
    obtain ⟨nA, hnA⟩ := common_bound (P := fun r n => ∀ c < p.ℓ,
        rejNTTPoly n (aSeed (vPk p σ) r c) = some (polyAt s.mem (pa s (pA p.ℓ r c))))
      (fun _ _ _ hle h c hc => rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
        common_bound (P := fun c n => rejNTTPoly n (aSeed (vPk p σ) r c) = some (polyAt s.mem (pa s (pA p.ℓ r c))))
          (fun _ _ _ hle h => rejNTTPoly_mono hle h) p.ℓ fun c hc =>
            let ⟨b, hb⟩ := hA r hr c hc; ⟨b.rejNTT, hb⟩
    obtain ⟨bB, hbB⟩ := hB
    obtain ⟨cc, hcc, hcc'⟩ := Option.map_eq_some_iff.mp hbB
    have hl : h.length = p.k := hs.hint.1
    have e := verifyMu_rows p ⟨0, 0, nA, bB.ball⟩ (vPk p σ) (vMu σ) (vSig p σ) hh hl hnA hcc
    obtain ⟨hg, hβ, _, _⟩ := parChk p hp
    rw [decide_eq_true ((normR_vZ_iff hβ p hg _).mpr hn), hcc', Bool.true_and] at e
    by_cases hE : H (vMu σ ++ w1Enc p σ h (fun r c => polyAt s.mem (pa s (pA p.ℓ r c))) (ntt (polyAt s.mem (pa s pC))))
        p.ctildeLen = vCt p (vSig p σ)
    · exact .inl ⟨by rw [h15']; exact flag_congr (by simp [hE]),
        ⟨_, e.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
    · exact .inr ⟨by rw [h15']; exact flag_congr (by simp [hE]),
        false_ne (e.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩

theorem body_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {s : State} (ht : T p σ s) : WP isa (body P p) s (Fin p σ) := by
  unfold body
  refine WP.seq (WP.mono (hint_ok C hp hv ht) fun s₁ ⟨t₁, hm⟩ => ?_)
  split at hm
  · rename_i h hh
    obtain ⟨h15₁, hH⟩ := hm
    refine ifOk_ok (p := True) h15₁ (fun s₂ hP₂ e₂ _ => ?_) fun _ _ _ h => absurd trivial h
    obtain ⟨_, _, kh, _⟩ := parChk p hp
    have S : S2 p h 0 σ s₂ := ⟨t₁.step hp hv hP₂ (tChk_nil p hp), (t₁.lay hp hv).keepHint hP₂ kh hH,
      fun _ h => absurd h (Nat.not_lt_zero _), by rw [e₂, h15₁]; exact flag_congr (by simp)⟩
    refine WP.seq (WP.mono (seqR_ok (I := fun i => S2 p h i σ) p.ℓ 0
      (fun i _ hi st hst => zOne_ok C hp hv (by omega) hst) s₂ S) fun s₃ hs₃ => ?_)
    rw [Nat.zero_add] at hs₃
    refine ifOk_ok hs₃.r15 (fun s₄ hP₄ e₄ hn => ?_) fun s₄ hP₄ e₄ hn => ?_
    · refine WP.seq (WP.mono (samples_ok C hp hv (hs₃.flag hp hv (Nat.le_refl _) hP₄ e₄)
        (by rw [e₄, hs₃.r15]; exact flag_congr (iff_true_intro hn))) fun s₅ hs₅ => cs_ok C hp hv hh hn hs₅)
    · obtain ⟨hg, hβ, _, _⟩ := parChk p hp
      exact ⟨hs₃.t.step hp hv hP₄ (tChk_nil p hp), .inr ⟨by rw [e₄, hs₃.r15]; exact flag_congr (iff_false_intro hn),
        verifyMu_norm minBounds _ _ hh (by rw [normR_vZ_iff hβ p hg]; exact hn)⟩⟩
  · rename_i hh
    refine ifOk_ok (p := False) hm (fun _ _ _ h => h.elim) fun s₂ hP₂ e₂ _ =>
      ⟨t₁.step hp hv hP₂ (tChk_nil p hp), .inr ⟨by rw [e₂]; exact hm, ?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [verifyMu_hint_none minBounds _ _ hh]
    nofun

theorem verify_correct {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) (σ : State) (hv : VPre p σ) :
    ∃ t s', Exec isa (verify P p) σ t s' ∧ abiPreserved σ s' ∧ (verifyK p).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp hv) fun s₁ ⟨h₁, _⟩ =>
    WP.seq (WP.mono (body_ok C hp hv h₁) fun s₂ ⟨h₂, hr⟩ =>
      WP.mono (epi_ok hp hv h₂) fun s₃ ⟨hres, hg⟩ =>
        (⟨hg, by
          rcases hr with ⟨e, hb⟩ | ⟨e, hb⟩
          · exact .inl ⟨by rw [hres, e]; rfl, hb⟩
          · exact .inr ⟨by rw [hres, e]; rfl, hb⟩⟩ : gprPreserved σ s₃ ∧ (verifyK p).post σ s₃)))
  exact ⟨t, s', he, abiPreserved_of_ctl (verify_ctl C hp) he hF.1, hF.2⟩

end VG.Proof.MlDsa.X86_64.Verify
