import VerifiedGarbage.Proof.MlDsa.X86.Verify.Samp

/-!
# ML-DSA verification on x86 (32-bit): `Â` and `c`

`ρ` copied to the seed, the rows of `Â` (`aRow_piece`), then `c =
SampleInBall(c̃)` masked with its result (`samples_piece`): from the result 1
to `SC`.
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly sampleInBall PolyIs Reduced polyAt toRq)
open VG.Proof.MlDsa.Verify (vZ vHint vRho vCt aSeed)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- After `SampleInBall`. -/
structure SB (s₀ s : State) : Prop where
  vb : VB p s₀ s
  ex : ∃ A : Nat → Nat → Poly, (∀ r s', Before p (8 * p.k) r s' → PolyIs s.mem (Buf.addr s₀ (pA r s')) (A r s')) ∧
    GA p s₀ (8 * p.k) A (accV s₀ s)
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ pC)
  out : Spec.MlDsa.Outcome (fun b => (sampleInBall p.τ b.ball (vCt p (vSig p s₀))).map toRq) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ pC))

end

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hF

theorem rho_piece : VP p (fun s₀ s => VB p s₀ s ∧ accV s₀ s = 1) (SA p · 0) (copyW vS ⟨0, 0, 32⟩ (sb oSB 32) 8) :=
  copyW_piece (Y := YV p) 0 0 vS oSB 8 (by decide) (by decide) (by lv hF) (h₁ := .block []) (by kernel_rfl)
    (by taint_decide) (fun _ _ _ h => h.1.ctx) fun s₀ s s' hp h h' fr cp => by
      have fr' : Frame (FR s₀ [sb oSB 32] 0) s.mem s'.mem := fr1 fr
      refine ⟨h.1.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) fr' h', ?_,
        fun _ _ => toRq Proof.MlDsa.KeyGen.zeroI, fun r s hb => absurd hb.2 (by omega),
        .inl ⟨by rw [acc_keepV hp (N := 0) (by omega) (by lv hF) fr']; exact h.2, minBounds,
          fun r s hb => absurd hb.2 (by omega)⟩⟩
      rw [show (32 : Nat) = 4 * 8 from rfl, cp, ← show (32 : Nat) = 4 * 8 from rfl,
        pk_slice hF hp h.1.ctx (by lv hF), List.drop_zero]
      rfl

include hP

theorem ball_call : VP p (SA p · (8 * p.k)) (SB p)
    (Impl.MlDsa.X86.KeyGen.callPR vS "vg_mldsa_sample_in_ball" P.ball
      [.buf ⟨2, 0, p.ctildeLen⟩, .imm p.ctildeLen, .imm p.τ, .buf pC, .buf (ssB 2048)]) :=
  ball_piece (Y := YV p) hP.ball 2 0 p.ctildeLen p.τ vS (oP 15) vS oSS hF.ball (by lv hF)
    (Nat.le_of_eq (YV_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.vb.ctx)
    (fun s₀ s₀' s s' hp hp' hq h h' => by
      rw [sig_slice hF hp h.vb.ctx (by lv hF), sig_slice hF hp' h'.vb.ctx (by lv hF), (inputs_pub hq).2.2])
    fun s₀ s s' hp h h' fr red out => by
      obtain ⟨A, hA, hG⟩ := h.ex
      refine ⟨h.vb.keep hp (N := 80) (by omega) (by lv hF) (fun j hj => by lv hF) fr h',
        ⟨A, fun r s hb => keepPolyD hp (stkV (by omega)) (by have := hb.1; have := hb.2; lv hF) fr (hA r s hb), ?_⟩,
        red, ?_⟩
      · rw [acc_keepV hp (N := 80) (by omega) (by lv hF) fr]; exact hG
      · rw [sig_slice hF hp h.vb.ctx (by lv hF), List.drop_zero] at out
        exact out

omit hP in
theorem ball_mask : VP p (SB p) (SC p) (maskA oACC (oP 15)) := by
  have hl := hF.l
  refine maskA_piece (Y := YV p) oACC (oP 15) (by lv hF) (maskA_tt _) (fun _ _ _ h => h.vb.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_
  simp only [YV_sc] at fr ha hc
  obtain ⟨A, hA, hG⟩ := h.ex
  have r01 : s.gpr .eax = 0 ∨ s.gpr .eax = 1 := by
    rcases h.out with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨m1, m0⟩ := Proof.MlDsa.KeyGen.masked r01 hc
  have a01 : accV s₀ s = 0 ∨ accV s₀ s = 1 := by
    rcases hG with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨-, aiff⟩ := Proof.MlDsa.KeyGen.acc_and a01 r01
  have fr' : Frame (FR s₀ [sb oACC 4, pC] 0) s.mem s'.mem := fr2 fr
  have ea : accV s₀ s' = accV s₀ s &&& s.gpr .eax := ha
  have bf : ∀ r < p.k, ∀ s < p.ℓ, Before p (8 * p.k) r s := fun r hr s hs => ⟨hs, by omega⟩
  refine ⟨h.vb.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) fr' h', A,
    polyAt s'.mem (Buf.addr s₀ pC), fun r hr s hs => keepPolyD hp (stkV (by omega)) (by lv hF) fr'
      (hA r s (bf r hr s hs)), ⟨?_, rfl⟩, ?_⟩
  · rcases r01 with e0 | e1
    · exact (m0 e0).1
    · exact (m1 e1).2.2 (h.red e1)
  · rw [ea]
    rcases hG with ⟨h1, b, hb⟩ | ⟨h0, hn⟩
    · rcases h.out with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · obtain ⟨c, hc, hcC⟩ := Option.map_eq_some_iff.mp hb'
        refine .inl ⟨aiff.mpr ⟨h1, ho⟩, Proof.MlDsa.Verify.bmax b b', c, fun r hr s hs =>
          Proof.MlDsa.Verify.rejNTTPoly_mono (Proof.MlDsa.Verify.bmax_left b b').rejNTT (hb r s (bf r hr s hs)),
          Proof.MlDsa.Verify.sampleInBall_mono (Proof.MlDsa.Verify.bmax_right b b').ball hc, ?_⟩
        rw [hcC, (m1 ho).2.1]
      · rw [ho, h1]
        obtain ⟨hh, ehh, -⟩ := h.vb.hint
        refine .inr ⟨by decide, ?_⟩
        show Spec.MlDsa.verifyMu p minBounds (vPk p s₀) (vMu s₀) (vSig p s₀) ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_ball_none minBounds _ _ ehh (Option.map_eq_none_iff.mp hn)]
        exact fun h => nomatch h
    · rw [h0]
      exact .inr ⟨BitVec.zero_and, hn⟩

theorem samples_piece : VP p (fun s₀ s => VB p s₀ s ∧ accV s₀ s = 1) (SC p) (samples P p) := by
  unfold samples
  refine (rho_piece hF).seq ?_
  refine Piece.seq (B := (SA p · (8 * p.k))) ((seqR_piece (I := fun r => (SA p · (8 * r))) p.k 0
    fun r _ hr => aRow_piece hP hF (by omega)).mono (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  exact (ball_call hP hF).seq (ball_mask hF)

end

end VG.Proof.MlDsa.X86.Verify
