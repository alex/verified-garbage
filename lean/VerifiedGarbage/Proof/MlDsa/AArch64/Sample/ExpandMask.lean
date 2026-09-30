import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMaskLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT

/-!
# ML-DSA on AArch64: `vg_mldsa_expand_mask_poly`

Untrusted: everything here is checked by Lean. Correctness: the prologue,
the sponge (640 bytes of SHAKE256 of the seed), the branch on `γ₁` to the
loop for `c = 18` or `20` (`ExpandMaskLoop.lean`), and the epilogue.
Constant time: the prologue, and then everything else, by the taint
analysis (the second from registers that correctness makes equal: the
pointers and `γ₁`, which the prologue zero-extends from `w1`).
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_lsr toNat_lsr eval_zero eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H PolyIs coeffAt toRq bitUnpack bitlen)
open VG.Spec.Sha3 (bytesAt)

/-- `γ₁`, the `u32` argument in `w1`. -/
abbrev gammaOf (s : State) : Nat := ((s.gpr .x1).setWidth 32).toNat

/-- `vg_mldsa_expand_mask_poly(seed = x0, gamma1 = w1, a = x2, scratch = x3)`,
with 16 bytes of stack below `sp`. -/
def emK : Contract isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 66⟩
    let a : Region := ⟨s.gpr .x2, 1024⟩
    let scratch : Region := ⟨s.gpr .x3, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [a, scratch] ∧ seed.Disjoint a ∧ seed.Disjoint scratch ∧
    a.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint a ∧
    stack.Disjoint scratch ∧ (gammaOf s = 2 ^ 17 ∨ gammaOf s = 2 ^ 19)
  post s s' :=
    PolyIs s'.mem (s.gpr .x2) (toRq (bitUnpack (H (bytesAt s.mem (s.gpr .x0) 66)
      (32 * (1 + bitlen (gammaOf s - 1)))) (gammaOf s - 1) (gammaOf s)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ (s₁.gpr .x1).setWidth 32 = (s₂.gpr .x1).setWidth 32 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

namespace ExpandMask

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .x0, 66, σ.gpr .x3, σ.gpr .x2, ((σ.gpr .x1).setWidth 32).setWidth 64⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H ((spOf σ).msg σ) 640

section
variable {σ : State} (hp : emK.pre σ)
include hp

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, by show (66 : Nat) < 2 ^ 64; decide⟩

theorem gamma : gammaOf σ = 2 ^ 17 ∨ gammaOf σ = 2 ^ 19 := hp.2.2.2.2.2.2.2.2.2

theorem pro_ok : WP isa (.block (pro .x3 .x2 (.addImm .w .x27 .x1 0) (.movz .x .x4 66 0))) σ (J0 (spOf σ) σ) :=
  Sample.pro_ok (spOk hp) rfl rfl (by decide) rfl
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, ite_true, hs .x1 (by decide) (by decide)]
      congr 1
      exact BitVec.add_zero _⟩)
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)

omit hp in
theorem x27_toNat {s : State} (h : Env (spOf σ) σ s) : (s.gpr .x27).toNat = gammaOf σ := by
  rw [h.x27]; simp; omega

/-- The loop for `c`. -/
theorem loop_ok' {s : State} (h : J6 136 640 (spOf σ) σ s) {c : Nat} (hc : c = emC (gammaOf σ)) :
    WP isa (emLoop c) s fun s' => Env (spOf σ) σ s' ∧
      ∀ i < 256, coeffAt s'.mem (σ.gpr .x2) i = ExpandMask.Wd (X σ) c i := by
  have hg := gamma hp
  obtain ⟨_, _, e3⟩ := emC_eq hg
  have hc' : c = 18 ∨ c = 20 := by subst hc; unfold emC; split <;> simp
  have lp : ExpandMask.LPre (X σ) c ((spOf σ).at' 840) (σ.gpr .x2) s :=
    ⟨hc', H_length _ _, fun p hp' => by rw [X, H_eq, ← h.out, MlKem.bytesAt_getD _ _ hp'],
      fun p hp' => by rw [at_add]; exact inScrRd (spOk hp) h.env.rd h.env.wr (by omega),
      fun g hg' => by
        rw [at_add]; exact inScrRd (spOk hp) h.env.rd h.env.wr (by rcases hc' with rfl | rfl <;> omega),
      fun i hi => inA (spOk hp) h.env.wr hi, (a_scr' (spOk hp) (by omega)).symm, by rw [h.env.x25],
      h.env.x26, by rw [x27_toNat h.env, e3, hc]⟩
  exact WP.mono (ExpandMask.loop_ok lp) fun u hu => ⟨h.env.keepA (spOk hp) hu.keep hu.frame, hu.st⟩

end

theorem correct (σ : State) (hp : emK.pre σ) :
    ∃ t s', Exec isa expandMask σ t s' ∧ abiPreserved σ s' ∧ emK.post σ s' := by
  have hg := gamma hp
  obtain ⟨e1, e2, e3⟩ := emC_eq hg
  refine WP.seq (WP.mono (pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 136) (outlen := 640) (by decide) (by decide) h1)
      fun s h2 => ?_))
  refine WP.seq (WP.mono (Q := fun (u : State) => Env (spOf σ) σ u ∧
    ∀ i < 256, coeffAt u.mem (σ.gpr .x2) i = ExpandMask.Wd (X σ) (emC (gammaOf σ)) i) ?_
    fun u ⟨he, hst⟩ => WP.mono (epi_ok (spOk hp) he) fun s' ⟨abi, m, _⟩ => ⟨abi, by
      show PolyIs s'.mem _ _
      rw [m]
      refine polyIs_of_coeffAt fun i hi => ?_
      rw [hst i hi, expandMask_getElem _ hg hi, ExpandMask.Wd, ExpandMask.F, ← e3]⟩)
  refine WP.seq (wp_lsr (by decide) fun s₁ o₁ e₁ => wp_nil ?_)
  -- the branch on `γ₁`
  have x9 : (s₁.gpr .x9).toNat = gammaOf σ / 2 ^ 18 := by
    rw [e₁, toNat_lsr, x27_toNat h2.env]
  have h6 : J6 136 640 (spOf σ) σ s₁ := ⟨h2.env.keep o₁.keep o₁.mem, by rw [o₁.mem]; exact h2.out⟩
  rcases hg with hg | hg
  · have ec : emC (gammaOf σ) = 18 := by unfold emC; rw [hg]; rfl
    refine WP.ite true (by rw [eval_zero, eq_zero_iff, x9, hg]; rfl) (fun _ => ?_) (fun h => nomatch h)
    rw [ec]; exact loop_ok' hp h6 ec.symm
  · have ec : emC (gammaOf σ) = 20 := by unfold emC; rw [hg]; rfl
    refine WP.ite false (by rw [eval_zero, eq_zero_iff, x9, hg]; rfl) (fun h => nomatch h) (fun _ => ?_)
    rw [ec]; exact loop_ok' hp h6 ec.symm

/-! ## Constant time -/

theorem pub_eq {σ₁ σ₂ : State} (hq : emK.pub σ₁ σ₂) : spOf σ₁ = spOf σ₂ := by
  rw [spOf, spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]

theorem ct : ConstantTime isa emK.pre emK.pub expandMask := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True)
    (P := Rel2 emK.pre emK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (spOf σ) σ) [.x0, .x2, .x3]
    (fun σ s hp h => by subst h; exact pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂
      exact ⟨hq.2.2.2.2, RejNtt.regs3 hq.1 hq.2.2.1 hq.2.2.2.1⟩) (by taint_decide)) ?_
  exact relTaint [.x25, .x26, .x27, .x3, .x4] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, pub_eq hq]
      · rw [h₁.x3, h₂.x3, pub_eq hq]
      · exact toNat_inj h₁.x4 h₂.x4) (by taint_decide)

end ExpandMask

/-- A state satisfying the precondition. -/
def emSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x20000 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem expandMask_verified : Verified AArch64.target Impl.MlDsa.AArch64.Sample.expandMask
    (Spec.MlDsa.expandMaskContract AArch64.abi 16) :=
  Verified.of_correct ExpandMask.correct ExpandMask.ct
    { pre := by sig_implies_pre [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, emK,
        AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, emK,
        AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, emK,
        AArch64.abi, AArch64.argRegs]
      sat := by sig_implies_sat [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, emK,
        AArch64.abi, AArch64.argRegs] [emSat] using emSat }

end VG.Proof.MlDsa.AArch64.Sample
