import VerifiedGarbage.Proof.MlDsa.X86.Verify.Ball

/-!
# ML-DSA verification on x86 (32-bit): what holds while computing `w′₁`

From the hint `h`, `Â` (`A`) and `c` (`C`) the samplers gave, `CX` says what
`scratch` holds while computing: `ẑ[i]` for `i < j` (and `z[i]` for the
others), `ĉ` once `cd`, and the packed rows `w₁[r]` for `r < nr`; and the
result (`GC`). It is kept by pieces that write only buffers apart from those
(`SafeC`, `CX.keep`). The NTTs of `z` and `c` (`nttZ_piece`, `nttC_piece`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly PolyIs Reduced polyAt toRq ntt HintIs simpleBitPack)
open VG.Proof.MlDsa.Verify (vZ vHint zHat w1Row)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params) (s₀ : State)

/-- The row `r` of `w₁` packed in `scratch`. -/
abbrev wB (r : Nat) : Buf := sb (oB + w1Len p * r) (w1Len p)

/-- While computing `w′₁`, with the hint `h`, `Â` and `c` of the samplers. -/
structure CX (h : List (Vector Bool Spec.MlDsa.n)) (A : Nat → Nat → Poly) (C : Poly) (j : Nat) (cd : Bool)
    (nr : Nat) (s : State) : Prop where
  ctx : Ctx (YV p) s₀ s
  norms : NormsOk p s₀ p.ℓ
  hh : hOf p s₀ = some h
  hint : HintIs s.mem (Buf.addr s₀ (hB p.k)) p.k h
  a : ∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pA r s')) (A r s')
  z : ∀ i < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pZ i))
    (if i < j then zHat p (vSig p s₀) i else toRq (vZ p (vSig p s₀) i))
  c : PolyIs s.mem (Buf.addr s₀ pC) (if cd then ntt C else C)
  gc : GC p s₀ A C (accV s₀ s)
  w : ∀ r < nr, bytesAt s.mem (Buf.addr s₀ (wB p r)) (w1Len p) =
    simpleBitPack (w1Row p (vPk p s₀) (vSig p s₀) A (ntt C) h r) (w1Max p)

/-- While computing `w′₁`. -/
def CI (j : Nat) (cd : Bool) (nr : Nat) (s : State) : Prop :=
  ∃ h A C, CX p s₀ h A C j cd nr s

end

/-- The buffers of `CX` but `z` and `c` are apart from `bs`. -/
structure SafeC (p : Params) (nr : Nat) (bs : List Buf) : Prop where
  h : (YV p).apart (hB p.k) bs = true
  a : ∀ r < p.k, ∀ s < p.ℓ, (YV p).apart (pA r s) bs = true
  acc : (YV p).apart (sb oACC 4) bs = true
  w : ∀ r < nr, (YV p).apart (wB p r) bs = true

/-- `CX` after a piece that writes only `bs`, with `z` and `c` as they are after it. -/
theorem CX.update {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → Poly} {C : Poly} {j : Nat}
    {cd : Bool} {nr : Nat} {s₀ s s' : State} (hc : CX p s₀ h A C j cd nr s) (hp : TPre (YV p) s₀)
    {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96) (sf : SafeC p nr bs) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : Ctx (YV p) s₀ s') {j' : Nat} {cd' : Bool}
    (hz : ∀ i < p.ℓ, PolyIs s'.mem (Buf.addr s₀ (pZ i))
      (if i < j' then zHat p (vSig p s₀) i else toRq (vZ p (vSig p s₀) i)))
    (hcc : PolyIs s'.mem (Buf.addr s₀ pC) (if cd' then ntt C else C)) : CX p s₀ h A C j' cd' nr s' :=
  ⟨h', hc.norms, hc.hh, keepHint hp hN sf.h fr hc.hint,
    fun r hr s hs => keepPolyD hp (stkV hN) (sf.a r hr s hs) fr (hc.a r hr s hs), hz, hcc,
    by rw [acc_keepV hp hN sf.acc fr]; exact hc.gc,
    fun r hr => by rw [keepBytes hp (stkV hN) (sf.w r hr) fr]; exact hc.w r hr⟩

/-- `CX` after a piece that writes only `bs`, apart from `z` and `c`. -/
theorem CX.keep {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → Poly} {C : Poly} {j : Nat}
    {cd : Bool} {nr : Nat} {s₀ s s' : State} (hc : CX p s₀ h A C j cd nr s) (hp : TPre (YV p) s₀)
    {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96) (sf : SafeC p nr bs)
    (sz : ∀ i < p.ℓ, (YV p).apart (pZ i) bs = true) (sc : (YV p).apart pC bs = true)
    (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : Ctx (YV p) s₀ s') : CX p s₀ h A C j cd nr s' :=
  hc.update hp hN sf fr h' (fun i hi => keepPolyD hp (stkV hN) (sz i hi) fr (hc.z i hi))
    (keepPolyD hp (stkV hN) sc fr hc.c)

theorem w_row {p : Params} {r : Nat} (hr : r < p.k) : w1Len p * r + w1Len p ≤ p.k * w1Len p := by
  rw [Nat.mul_comm p.k]; exact mul_row hr

theorem w_rows {p : Params} {r nr : Nat} (hr : r < nr) (hnr : nr ≤ p.k) :
    w1Len p * r + w1Len p ≤ w1Len p * nr ∧ w1Len p * r + w1Len p ≤ p.k * w1Len p :=
  ⟨mul_row hr, w_row (Nat.lt_of_lt_of_le hr hnr)⟩

/-- Proves `SafeC` for buffers checked by `lv`, with `hnr : nr ≤ p.k`. -/
macro "safeC " hF:term:max hnr:term:max : tactic => `(tactic| exact
  ⟨by lv $hF, fun r hr s hs => by lv $hF, by lv $hF, fun r hr => by
    have := VG.Proof.MlDsa.X86.Verify.w_rows hr $hnr
    lv $hF⟩)

theorem ci_of_sc {p : Params} {s₀ s : State} (h : SC p s₀ s) : CI p s₀ 0 false 0 s := by
  obtain ⟨hh, ehh, hi⟩ := h.vb.hint
  obtain ⟨A, C, hA, hC, hG⟩ := h.ex
  exact ⟨hh, A, C, h.vb.ctx, h.vb.norms, ehh, hi, hA, fun i hi => by
    rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero _)]; exact h.vb.z i hi, hC, hG,
    fun r hr => absurd hr (Nat.not_lt_zero _)⟩

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

theorem nttZ_piece {j : Nat} (hj : j < p.ℓ) :
    VP p (CI p · j false 0) (CI p · (j + 1) false 0) (nttAt P (pZ j)) :=
  inPlace_piece (Y := YV p) hP.ntt vS (oP (8 + j)) vS oSS (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h⟩ => ⟨h.ctx, by have := (h.z j hj).1; exact this⟩)
    fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr post => by
      refine ⟨hh, A, C, h.update hp (N := 80) (by omega) (by safeC hF (Nat.zero_le p.k)) fr h' (fun i hi => ?_)
        (keepPolyD hp (stkV (by omega)) (by lv hF) fr h.c)⟩
      rcases (by omega : i < j ∨ i = j ∨ j < i) with hij | rfl | hij
      · have e := keepPolyD hp (stkV (by omega)) (by lv hF) fr (h.z i hi)
        simp only [hij, show i < j + 1 by omega, ite_true] at e ⊢
        exact e
      · rw [ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self i) h]
        have e := (h.z i hi).2
        rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl _)] at e
        rw [e] at post
        exact post
      · have e := keepPolyD hp (stkV (by omega)) (by lv hF) fr (h.z i hi)
        simp only [show ¬ i < j by omega, show ¬ i < j + 1 by omega, ite_false] at e ⊢
        exact e

theorem nttC_piece : VP p (CI p · p.ℓ false 0) (CI p · p.ℓ true 0) (nttAt P pC) :=
  inPlace_piece (Y := YV p) hP.ntt vS (oP 15) vS oSS (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h⟩ => ⟨h.ctx, h.c.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr post => by
      refine ⟨hh, A, C, h.update hp (N := 80) (by omega) (by safeC hF (Nat.zero_le p.k)) fr h'
        (fun i hi => keepPolyD hp (stkV (by omega)) (by lv hF) fr (h.z i hi)) ?_⟩
      have e := h.c.2
      simp only [Bool.false_eq_true, ite_false] at e
      rw [e] at post
      simpa using post

end

end VG.Proof.MlDsa.X86.Verify
