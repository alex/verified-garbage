import VerifiedGarbage.Proof.MlDsa.X86.Verify.Final
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp

/-!
# ML-DSA verification on x86 (32-bit): the body

The body, piece by piece (`body_piece`), for any parameter set of Table 1 and
any verified implementations of the primitives: `HintBitUnpack`, a branch on
its result (which depends only on the signature), `z` and its norms, a branch
on them (which depend only on the signature), the samplers and the rest; it
returns the result, as the contract says (`VFin`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Impl.MlDsa.X86.KeyGen (seqR)
open VG.Spec.MlDsa (Params minBounds)
open VG.Spec.Sha3 (bytesAt)

/-- The body's end: the postcondition, and `eax` the result. -/
abbrev Done (p : Params) (s₀ s : State) : Prop := VFin p s₀ s ∧ s.gpr .eax = accV s₀ s

theorem hOf_pub {p : Params} {s₀ s₀' : State} (hq : TPub (YV p) (lkV p) s₀ s₀') : hOf p s₀ = hOf p s₀' := by
  simp only [hOf, (inputs_pub hq).2.2]

theorem norms_pub {p : Params} {s₀ s₀' : State} (hq : TPub (YV p) (lkV p) s₀ s₀') :
    decide (NormsOk p s₀ p.ℓ) = decide (NormsOk p s₀' p.ℓ) := by
  simp only [NormsOk, (inputs_pub hq).2.2]

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

/-- Once the norms of `z` are within the bound. -/
theorem ok2_piece : VP p (fun s₀ s => ZI p s₀ p.ℓ s ∧ decide (NormsOk p s₀ p.ℓ) = true) (VFin p)
    (.seq (samples P p) (compute P p)) :=
  ((samples_piece hP hF).mono (fun _ _ _ ⟨h, hn⟩ => by
    have hn := of_decide_eq_true hn
    exact ⟨⟨h.ctx, h.hint, h.z, hn⟩, by rw [h.acc, ifp hn _ _]⟩) fun _ _ _ h => h).seq (compute_piece hP hF)

/-- Once the hint is well formed. -/
theorem ok1_piece : VP p (fun s₀ s => H1 p s₀ s ∧ (hOf p s₀).isSome = true) (VFin p)
    (.seq (seqR (zOne P p) 0 p.ℓ) (ifOk (.seq (samples P p) (compute P p)))) := by
  refine Piece.seq (B := (ZI p · p.ℓ)) ((seqR_piece (I := fun i => (ZI p · i)) p.ℓ 0
    fun i _ hi => zOne_piece hP hF (by omega)).mono (fun s₀ s _ ⟨h, hs⟩ => ?_) fun _ _ _ h => by simpa using h) ?_
  · rcases h.2 with ⟨e, ho⟩ | ⟨_, hn⟩
    · exact ⟨h.1, ho, fun j hj => absurd hj (Nat.not_lt_zero _), by
        rw [e, ifp (fun j hj => absurd hj (Nat.not_lt_zero _)) _ _]⟩
    · rw [hn] at hs; exact absurd hs (by decide)
  refine ifOk_piece (Y := YV p) (fun s₀ => decide (NormsOk p s₀ p.ℓ)) (by lv hF) (by taint_decide)
    (fun _ _ _ h => h.ctx) (fun s₀ s s' _ h h' m => ⟨h', ?_, ?_, ?_⟩) (fun s₀ s _ h => ?_)
    (fun _ _ _ _ hq => norms_pub hq) (ok2_piece hP hF) fun s₀ s _ h hn => ⟨h.ctx, .inr ⟨?_, ?_⟩⟩
  · obtain ⟨hh, e, hi⟩ := h.hint; exact ⟨hh, e, by rw [m]; exact hi⟩
  · intro j hj; rw [m]; exact h.z j hj
  · rw [accV, m]; exact h.acc
  · show (accV s₀ s != 0) = _
    rw [h.acc]
    by_cases hn : NormsOk p s₀ p.ℓ
    · rw [ifp hn _ _, decide_eq_true hn]; rfl
    · rw [ifn hn _ _, decide_eq_false hn]; rfl
  · rw [h.acc, ifn (of_decide_eq_false hn) _ _]
  · obtain ⟨hh, e, -⟩ := h.hint
    show Spec.MlDsa.verifyMu p minBounds (vPk p s₀) (vMu s₀) (vSig p s₀) ≠ some true
    exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e fun hlt =>
      of_decide_eq_false hn ((Proof.MlDsa.Verify.normR_vZ_iff hF.beta.1 p hF.g1 _).mp hlt)

omit hP in
theorem ret_piece : VP p (VFin p) (Done p) (.block [.mov .eax (.mem (at_ .esi oACC))]) :=
  ld32_piece (Y := YV p) oACC (by lv hF) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
    fun s₀ s s' _ h h' m e => ⟨⟨h', by rw [accV, m]; exact h.2⟩, by rw [e, accV, m]; rfl⟩

theorem body_piece : VP p (fun s₀ s => s = P0 s₀) (Done p) (body P p) := by
  unfold body
  refine (ldsc_piece (Y := YV p) (ht := .block []) (by kernel_rfl)).seq ((hint_piece hP hF).seq ?_)
  refine Piece.seq (ifOk_piece (Y := YV p) (fun s₀ => (hOf p s₀).isSome) (by lv hF) (by taint_decide)
    (fun _ _ _ h => h.1) (fun s₀ s s' _ h h' m => ⟨h', ?_⟩) (fun s₀ s _ h => ?_) (fun _ _ _ _ hq => by
      rw [hOf_pub hq]) (ok1_piece hP hF) fun s₀ s _ h hn => ⟨h.1, .inr ⟨?_, ?_⟩⟩) (ret_piece hF)
  · rcases h.2 with ⟨e, hh, eh, hi⟩ | ⟨e, hn⟩
    · exact .inl ⟨by rw [accV, m]; exact e, hh, eh, by rw [m]; exact hi⟩
    · exact .inr ⟨by rw [accV, m]; exact e, hn⟩
  · show (accV s₀ s != 0) = _
    rcases h.2 with ⟨e, _, eh, _⟩ | ⟨e, hn⟩
    · rw [e, eh]; rfl
    · rw [e, hn]; rfl
  · rcases h.2 with ⟨_, _, eh, _⟩ | ⟨e, _⟩
    · rw [eh] at hn; simp at hn
    · exact e
  · have e : hOf p s₀ = none := by
      cases e : hOf p s₀ with
      | none => rfl
      | some _ => rw [e] at hn; simp at hn
    show Spec.MlDsa.verifyMu p minBounds (vPk p s₀) (vMu s₀) (vSig p s₀) ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ e]
    exact fun h => nomatch h

end

/-! ## The stack -/

theorem NoSp.ite {cnd : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite cnd a b) := fun i hi => by
  simp only [X86.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem NoSp.ifOk {c : Prog isa} (hc : NoSp c) : NoSp (ifOk c) :=
  NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.ite hc (NoSp.of_all (by kernel_rfl)))

theorem body_nosp {P : Prims} (hP : PrimsOk P) (p : Params) : NoSp (body P p) := by
  unfold body
  refine NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq ?_ (NoSp.seq (NoSp.ifOk (NoSp.seq (NoSp.seqR (fun i => ?_) _ _)
    (NoSp.ifOk (NoSp.seq ?_ ?_)))) (NoSp.of_all (by kernel_rfl))))
  · unfold hint
    exact NoSp.seq (NoSp.callPR hP.hintUnpack.nosp) (NoSp.of_all (by kernel_rfl))
  · unfold zOne
    exact NoSp.seq (NoSp.callP hP.bitUnpack.nosp) (NoSp.seq (NoSp.callPR hP.normLt.nosp) (NoSp.of_all (by kernel_rfl)))
  · unfold samples
    refine NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.seqR (fun r => NoSp.seqR (fun e => ?_) _ _) _ _)
      (NoSp.seq (NoSp.callPR hP.ball.nosp) (NoSp.of_all (by kernel_rfl))))
    unfold aOne
    exact NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.seq (NoSp.of_all (by kernel_rfl))
      (NoSp.seq (NoSp.callPR hP.rejNtt.nosp) (NoSp.of_all (by kernel_rfl))))
  · unfold compute
    refine NoSp.seq (NoSp.seqR (fun i => NoSp.callP hP.ntt.nosp) _ _) (NoSp.seq (NoSp.callP hP.ntt.nosp)
      (NoSp.seq (NoSp.seqR (fun r => ?_) _ _) (NoSp.seq (NoSp.of_all (by kernel_rfl)) (NoSp.of_all (by kernel_rfl)))))
    unfold row
    exact NoSp.seq (NoSp.callP hP.mul.nosp) (NoSp.seq (NoSp.seqR (fun j => NoSp.callP hP.mulAdd.nosp) _ _)
      (NoSp.seq (NoSp.callP hP.unpackT1.nosp) (NoSp.seq (NoSp.callP hP.ntt.nosp) (NoSp.seq (NoSp.callP hP.mul.nosp)
        (NoSp.seq (NoSp.callP hP.sub.nosp) (NoSp.seq (NoSp.callP hP.invNtt.nosp) (NoSp.seq
          (NoSp.callP hP.useHint.nosp) (NoSp.callP hP.simpleBitPack.nosp))))))))

end VG.Proof.MlDsa.X86.Verify
