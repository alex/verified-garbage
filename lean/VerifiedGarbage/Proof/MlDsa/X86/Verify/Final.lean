import VerifiedGarbage.Proof.MlDsa.X86.Verify.Row
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds

/-!
# ML-DSA verification on x86 (32-bit): `c̃′` and the result

Untrusted: everything here is checked by Lean. `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)`
(`hash_piece`), and the result ANDed with `c̃′ = c̃` (`cmp_piece`): with the
samplers' outputs those of the standard for bounds `b`, the result is 1
exactly when `verifyMu` is true for `b` (`verifyMu_rows`), and it stays 0 if
verification is not true within the least bounds, which is the contract's
postcondition (`VFin`, `compute_piece`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly PolyIs polyAt toRq ntt HintIs simpleBitPack minBounds)
open VG.Proof.MlDsa.Verify (vZ vHint vCt w1Row)
open VG.Spec.Sha3 (bytesAt)

theorem flatMap_congr_mem' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem' fun y hy => h y (List.mem_cons_of_mem _ hy)]

section
variable (p : Params) (s₀ : State)

/-- `c̃′`, with the hint `h`, `Â` and `c` of the samplers. -/
abbrev ctOf (h : List (Vector Bool Spec.MlDsa.n)) (A : Nat → Nat → Poly) (C : Poly) : List Byte :=
  Spec.MlDsa.H (vMu s₀ ++ (List.range p.k).flatMap fun r =>
    simpleBitPack (w1Row p (vPk p s₀) (vSig p s₀) A (ntt C) h r) (w1Max p)) p.ctildeLen

/-- After the hash. -/
def CH (s : State) : Prop :=
  ∃ h A C, CX p s₀ h A C p.ℓ true p.k s ∧ bytesAt s.mem (Buf.addr s₀ (sb oCT p.ctildeLen)) p.ctildeLen = ctOf p s₀ h A C

end

section
variable {p : Params} (hF : VFacts p)
include hF

theorem hash_piece : VP p (CI p · p.ℓ true p.k) (CH p)
    (hash2 vS 0 200 136 0x1f ⟨1, 0, 64⟩ (sb oB (p.k * w1Len p)) (sb oCT p.ctildeLen)) := by
  have hw := hF.w1; have hct := hF.ct
  refine hash2_piece (Y := YV p) 0 200 136 0x1f ⟨1, 0, 64⟩ (sb oB (p.k * w1Len p)) (sb oCT p.ctildeLen)
    Proof.MlKem.rate136 (by lv hF) (by rw [YV_stk]; omega) (by decide) (by show p.k * w1Len p < 2 ^ 32; omega)
    (by show p.ctildeLen < 2 ^ 32; omega) (by taint_decide) (h₁ := .block []) (by kernel_rfl)
    (h₂ := .block []) (by kernel_rfl) (h₃ := .block []) (by kernel_rfl) (h₄ := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h⟩ => h.ctx) fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr out => ⟨hh, A, C,
      h.keep hp (N := 40) (by omega) (by safeC hF (Nat.le_refl p.k)) (fun i hi => by lv hF) (by lv hF) fr h', ?_⟩
  rw [out, sponge_H, Ctx.roBytes hp h.ctx (b := ⟨1, 0, 64⟩) (by lv hF) rfl]
  refine congrArg (fun x => Spec.MlDsa.H (vMu s₀ ++ x) p.ctildeLen) ?_
  have a0 := Buf.addr_eq hp (b := sb oB (p.k * w1Len p)) (by lv hF)
  show bytesAt s.mem (Buf.addr s₀ (sb oB (p.k * w1Len p))) (p.k * w1Len p) = _
  rw [a0, Nat.mul_comm, Proof.MlDsa.KeyGen.bytesAt_pieces]
  refine flatMap_congr_mem' fun r hr => ?_
  have hr := List.mem_range.mp hr
  have := w_rows hr (Nat.le_refl _)
  rw [← Buf.addr_eq hp (b := wB p r) (by lv hF)]
  exact h.w r hr

omit hF in
theorem mask_and {P : Prop} [Decidable P] {x : Bool} (hx : x = true ↔ P) :
    (1 : BitVec 32) &&& Proof.MlKem.X86.Decaps.mask P = if x then 1 else 0 := by
  by_cases hP : P
  · rw [show x = true from hx.mpr hP]; simp [Proof.MlKem.X86.Decaps.mask, hP]
  · rw [show x = false by cases x <;> simp_all]; simp [Proof.MlKem.X86.Decaps.mask, hP]

theorem cmp_piece' : VP p (CH p) (VFin p) (cmpAnd (sb oCT p.ctildeLen) ⟨2, 0, p.ctildeLen⟩ p.ctildeLen) := by
  have hct := hF.ct
  refine cmpAnd_piece (Y := YV p) (a := sb oCT p.ctildeLen) (b := ⟨2, 0, p.ctildeLen⟩) rfl (by lv hF) (by lv hF)
    (by lv hF) rfl (by show p.ctildeLen < 2 ^ 32; omega) (h₁ := .block []) (by kernel_rfl) (by taint_decide)
    (by taint_decide) (fun _ _ _ ⟨_, _, _, h, _⟩ => h.ctx) fun s₀ s s' hp ⟨hh, A, C, h, hct'⟩ h' m' => ⟨h', ?_⟩
  have ea : accV s₀ s' = accV s₀ s &&& Proof.MlKem.X86.Decaps.mask
      (ctOf p s₀ hh A C = vCt p (vSig p s₀)) := by
    rw [accV, m', acc_write]
    show _ &&& Proof.MlKem.X86.Decaps.mask (bytesAt s.mem (Buf.addr s₀ (sb oCT p.ctildeLen)) p.ctildeLen =
      bytesAt s.mem (Buf.addr s₀ ⟨2, 0, p.ctildeLen⟩) p.ctildeLen) = _
    rw [hct', sig_slice hF hp h.ctx (by lv hF), List.drop_zero]
    rfl
  rw [ea]
  rcases h.gc with ⟨h1, b, c, hA, hc, rfl⟩ | ⟨h0, hn⟩
  · have hv := Proof.MlDsa.Verify.verifyMu_rows p b (vPk p s₀) (vMu s₀) (vSig p s₀) h.hh h.hint.1 hA hc
    have hn : decide (Spec.MlDsa.normR ((List.range p.ℓ).map (vZ p (vSig p s₀))) < p.γ₁ - p.β) = true :=
      decide_eq_true ((Proof.MlDsa.Verify.normR_vZ_iff hF.beta.1 p hF.g1 _).mpr h.norms)
    rw [hn, Bool.true_and] at hv
    rw [h1]
    exact Proof.MlDsa.Verify.post_of_value (fun _ _ _ h₁ h₂ h => Proof.MlDsa.Verify.verifyMu_mono h₁ h₂ h) hv _
      (mask_and (by rw [beq_iff_eq]; exact eq_comm))
  · rw [h0]
    exact .inr ⟨BitVec.zero_and, hn⟩

end

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

theorem compute_piece : VP p (SC p) (VFin p) (compute P p) := by
  have hl := hF.l; have hk := hF.k
  unfold compute
  refine Piece.seq (B := (CI p · p.ℓ false 0)) ((seqR_piece (I := fun j => (CI p · j false 0)) p.ℓ 0
    fun j _ hj => nttZ_piece hP hF (by omega)).mono (fun _ _ _ h => ci_of_sc h)
      fun _ _ _ h => by simpa using h) ?_
  refine (nttC_piece hP hF).seq ?_
  refine Piece.seq (B := (CI p · p.ℓ true p.k)) ((seqR_piece (I := fun r => (CI p · p.ℓ true r)) p.k 0
    fun r _ hr => row_piece hP hF (by omega)).mono (fun _ _ _ h => h) fun _ _ _ h => by simpa using h) ?_
  exact (hash_piece hF).seq (cmp_piece' hF)

end

end VG.Proof.MlDsa.X86.Verify
