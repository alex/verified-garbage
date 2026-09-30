import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.BallLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT

/-!
# ML-DSA on AArch64: `vg_mldsa_sample_in_ball`

Untrusted: everything here is checked by Lean. Correctness: the prologue,
the sponge (272 bytes of SHAKE256 of `c̃`), `c` set to zeros, the loop
(`BallLoop.lean`), which leaves what `bFold` computes, and the end, which
returns whether `i` reached 256. Constant time up to `c̃`, as for
`vg_mldsa_rej_ntt_poly` (`RejNttCT.lean`): the loop, whose branches and
addresses depend on the output, by `memTaint`, since both runs have the same
output and zeros in `c`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_lsr ptr_add toNat_lsr agree_of)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H PolyIs coeffAt ballParams toRq n)
open VG.Spec.Sha3 (bytesAt)

/-- `τ`, the `u32` argument in `w2`. -/
abbrev tauOf (s : State) : Nat := ((s.gpr .x2).setWidth 32).toNat

/-- `vg_mldsa_sample_in_ball(ctilde = x0, len = x1, tau = w2, c = x3, scratch = x4) -> w0`,
with 16 bytes of stack below `sp`. -/
def sbK : Contract isa where
  pre s :=
    let ct : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let c : Region := ⟨s.gpr .x3, 1024⟩
    let scratch : Region := ⟨s.gpr .x4, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [ct] ∧ s.wr = [c, scratch] ∧ ct.Disjoint c ∧ ct.Disjoint scratch ∧
    c.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint ct ∧ stack.Disjoint c ∧
    stack.Disjoint scratch ∧ ((s.gpr .x1).toNat, tauOf s) ∈ ballParams
  post s s' :=
    (s'.gpr .x0).setWidth 32 =
        (if (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256 then 1 else 0) ∧
      ((ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256 →
        PolyIs s'.mem (s.gpr .x3)
          (toRq (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).1))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat = bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat

namespace Ball

theorem ballParams_le {len τ : Nat} (h : (len, τ) ∈ ballParams) : len ≤ 64 ∧ 39 ≤ τ ∧ τ ≤ 60 := by
  simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  omega

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .x0, (σ.gpr .x1).toNat, σ.gpr .x4, σ.gpr .x3, ((σ.gpr .x2).setWidth 32).setWidth 64⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H ((spOf σ).msg σ) 272

theorem X_length (σ : State) : (X σ).length = 272 := H_length _ _

section
variable {σ : State} (hp : sbK.pre σ)
include hp

theorem params : (σ.gpr .x1).toNat ≤ 64 ∧ 39 ≤ tauOf σ ∧ tauOf σ ≤ 60 :=
  ballParams_le hp.2.2.2.2.2.2.2.2.2

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, (σ.gpr .x1).isLt⟩

theorem pro_ok : WP isa (.block (pro .x4 .x3 (.addImm .w .x27 .x2 0) (mov .x4 .x1))) σ (J0 (spOf σ) σ) :=
  Sample.pro_ok (spOk hp) rfl rfl (by decide) rfl
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, ite_true, hs .x2 (by decide) (by decide)]
      congr 1
      exact BitVec.add_zero _⟩)
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, Size.bits, ite_true, BitVec.setWidth_eq, hs .x1 (by decide)
        (by decide) (by decide) (by decide), BitVec.add_zero]⟩)

/-- After the sponge, and `c` set to zeros. -/
structure Z (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  zero : ∀ i < 256, coeffAt s.mem (σ.gpr .x3) i = 0

theorem zero_ok {s : State} (h : J6 136 272 (spOf σ) σ s) : WP isa zeroPoly s (Z σ) :=
  WP.mono (zeroPoly_ok (fun i hi => inA (spOk hp) h.env.wr hi) h.env.x26) fun u ⟨k, z, f⟩ =>
    ⟨h.env.keepA (spOk hp) k f, by
      rw [MlKem.bytesAt_frame f (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (a_scr' (spOk hp) (by omega)).symm) (by omega), h.out,
        (H_eq _ _).symm], z⟩

theorem lpre {s : State} (h : Z σ s) : Ball.LPre (X σ) ((spOf σ).at' 840) (σ.gpr .x3) (tauOf σ) s :=
  ⟨fun p hp' => by rw [← h.out, MlKem.bytesAt_getD _ _ hp'],
    fun p hp' => by rw [at_add]; exact inScrRd (spOk hp) h.env.rd h.env.wr (by omega),
    inScrRd (spOk hp) h.env.rd h.env.wr (by omega),
    fun i hi => inA (spOk hp) h.env.wr hi, (a_scr' (spOk hp) (by omega)).symm,
    by rw [h.env.x25], h.env.x26, by rw [h.env.x27]; simp; omega,
    by have := (params hp).2.2; omega, h.zero⟩

/-- After the loop. -/
structure LP (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  x10 : (s.gpr .x10).toNat = (ballFold (tauOf σ) (X σ)).2
  st : CStored s.mem (σ.gpr .x3) (ballFold (tauOf σ) (X σ)).1

omit hp in
theorem St_264 : Ball.St (X σ) (tauOf σ) 264 = ballFold (tauOf σ) (X σ) := by
  simp only [Ball.St, ballFold]; rw [List.take_of_length_le (by rw [List.length_drop, X_length])]

theorem loopP_ok {s : State} (h : Z σ s) : WP isa bLoop s (LP σ) :=
  WP.mono (Ball.loop_ok (X_length σ) (by have := (params hp).2.2; omega) (lpre hp h)) fun u hu => by
    have x10 := hu.x10
    have st := hu.st
    rw [St_264] at x10 st
    exact ⟨h.env.keepA (spOk hp) hu.keep hu.frame, x10, st⟩

/-- The end: the postcondition, and the calling convention. -/
theorem end_ok {s : State} (h : LP σ s) :
    WP isa (.block (.lsr .x .x0 .x10 8 :: epi)) s fun s' => abiPreserved σ s' ∧ sbK.post σ s' := by
  refine wp_lsr (by decide) fun s₁ h₁ e₁ => ?_
  have hl : (ballFold (tauOf σ) (X σ)).2 ≤ 256 := bFold_le (by simp only [n]; omega) _
  have v0 : (s₁.gpr .x0).toNat = if (ballFold (tauOf σ) (X σ)).2 = 256 then 1 else 0 := by
    rw [e₁, toNat_lsr, h.x10]
    split <;> simp only [Nat.reducePow] <;> omega
  refine WP.mono (epi_ok (spOk hp) (h.env.keep h₁.keep h₁.mem)) fun s' ⟨abi, m, k⟩ => ⟨abi, ?_, fun hf => ?_⟩
  · rw [k.get .x0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, v0]
    split <;> rfl
  · rw [m, h₁.mem]
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [h.st i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map]

end

theorem correct (σ : State) (hp : sbK.pre σ) :
    ∃ t s', Exec isa sampleInBall σ t s' ∧ abiPreserved σ s' ∧ sbK.post σ s' :=
  WP.seq (WP.mono (pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 136) (outlen := 272) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (zero_ok hp h2) fun _ h3 =>
        WP.seq (WP.mono (loopP_ok hp h3) fun _ h4 => end_ok hp h4))))

end Ball

end VG.Proof.MlDsa.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H ballParams)
open VG.Spec.Sha3 (bytesAt)

namespace Ball

/-- The loop's regions. -/
abbrev lrd (σ : State) : List Region := [⟨(spOf σ).at' 840, 272⟩]
abbrev lwr (σ : State) : List Region := [polyR (σ.gpr .x3)]

theorem pub_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : spOf σ₁ = spOf σ₂ := by
  rw [spOf, spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]

theorem X_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : X σ₁ = X σ₂ := by
  simp only [X, Sp.msg]; rw [hq.2.2.2.2.2.2]

theorem loop_ct : RelCT isa (Rel2 sbK.pre sbK.pub Z) bLoop fun _ _ => True := by
  refine relMem lrd lwr [.x25, .x26, .x27]
    (fun σ₁ σ₂ _ _ hq => by simp [lrd, lwr, pub_eq hq, hq.2.2.2.1]) (fun σ s hp h => ?_)
    (fun σ s hp h => ?_) (fun σ₁ σ₂ s₁ s₂ p₁ p₂ hq h₁ h₂ => ?_) (by taint_decide)
  · rw [regions (spOk hp) h.env]
    refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
    · rcases mem2 hr with rfl | rfl
      · exact ⟨(spOf σ).scrR, by simp, 840, rfl, by simp⟩
      · exact ⟨polyR (σ.gpr .x3), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
    · rw [List.mem_singleton.mp hr, h.env.wr, (spOk hp).wr]
      exact ⟨polyR (σ.gpr .x3), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
  · have l := lpre hp h
    obtain ⟨t, u, e, -⟩ := Ball.loop_ok (X_length σ) (by have := (params hp).2.2; omega)
      (s₀ := s.withRegions (lrd σ) (lwr σ))
      ⟨l.buf, fun p hp' => Proof.MlKem.AArch64.in_rd (Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))),
        ⟨⟨(spOf σ).at' 840, 272⟩, by simp, by simp [Region.Contains]⟩,
        fun i hi => Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        l.disj, l.x25, l.x26, l.x27, l.tau, l.zero⟩
    exact ⟨t, u, e⟩
  · refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1], fun r hr => ?_, fun x hx => ?_⟩
    · rcases mem3 hr with rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, pub_eq hq]
    · obtain ⟨R, hR, hc⟩ := hx
      rcases mem2 hR with rfl | rfl
      · obtain ⟨p, hp', rfl⟩ := Proof.MlKem.AArch64.Sample.at_off hc
        rw [← MlKem.bytesAt_getD s₁.mem _ hp', h₁.out, pub_eq hq, ← MlKem.bytesAt_getD s₂.mem _ hp', h₂.out,
          X_eq hq]
      · rw [byte_zero h₁.zero hc, byte_zero h₂.zero (by rw [← hq.2.2.2.1]; exact hc)]

theorem ct : ConstantTime isa sbK.pre sbK.pub sampleInBall := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True)
    (P := Rel2 sbK.pre sbK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (spOf σ) σ) [.x0, .x1, .x3, .x4]
    (fun σ s hp h => by subst h; exact pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂
      refine ⟨hq.2.2.2.2.2.1, fun r hr => ?_⟩
      rcases mem4 hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.2.1, hq.2.2.2.2.1]) (by taint_decide)) ?_
  refine RelCT.seq (relTaintStep (J' := fun σ => J6 136 272 (spOf σ) σ) [.x25, .x26, .x27, .x3, .x4]
    (fun σ s hp h => sponge_ok (spOk hp) (by decide) (by decide) h) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, pub_eq hq]
      · rw [h₁.x3, h₂.x3, pub_eq hq]
      · exact toNat_inj h₁.x4 (by rw [h₂.x4, pub_eq hq])) (by taint_decide)) ?_
  refine RelCT.seq (relTaintStep (J' := Z) [.x26] (fun σ s hp h => zero_ok hp h)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1], fun r hr => by
      rw [List.mem_singleton.mp hr, h₁.env.x26, h₂.env.x26, pub_eq hq]⟩) (by taint_decide)) ?_
  refine RelCT.seq (relStep (J' := LP) (fun σ s hp h => loopP_ok hp h) loop_ct) ?_
  exact relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr, h₁.env.x25, h₂.env.x25, pub_eq hq]⟩) (by taint_decide)

end Ball

end VG.Proof.MlDsa.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition. -/
def sbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 32 | .x2 => 39 | .x3 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sampleInBall_verified : Verified AArch64.target Impl.MlDsa.AArch64.Sample.sampleInBall
    (Spec.MlDsa.sampleInBallContract AArch64.abi 16) :=
  Verified.of_correct Ball.correct Ball.ct
    { pre := by sig_implies_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK,
        AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi,
          AArch64.argRegs]
        dsimp only [sbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with ball := 272 }, by
            show Option.map _ (Spec.MlDsa.sampleInBall _ 272 _) = _
            rw [sampleInBall_some _ (by decide) hf, hpoly]; rfl⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.sampleInBall _ Spec.MlDsa.minBounds.ball _) = none
              rw [sampleInBall_none (B := 272) _ (by decide) (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi,
          AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2, hx3, hx4⟩ := h
        exact ⟨hx0, hx1, hx2, hx3, hx4, hsp, Proof.MlKem.AArch64.Sample.map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK,
        AArch64.abi, AArch64.argRegs] [sbSat] using sbSat }

end VG.Proof.MlDsa.AArch64.Sample
