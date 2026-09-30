import VerifiedGarbage.Proof.MlDsa.Arm.Verify.SampC

/-!
# ML-DSA verification on 32-bit ARM: after the samplers

Untrusted: everything here is checked by Lean. Once the samplers are done,
with `Â` and `c` in memory as `A'` and `cc` and `r11` as `R`, the rest of
the function computes `w′₁` from them, whatever they are (`KC5`): the first
`nz` of `z` in the NTT domain, `c` in it or not, and the first `nr` rows of
`w′₁` packed to `B`. Here: `ẑ[j] = NTT(z[j])` and `ĉ = NTT(c)`
(`nttZ_piece`, `nttC_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee ip_ok ip_tr
  polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD)
open VG.Impl.MlDsa.Arm.Verify
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt Reduced ntt simpleBitPack)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: `w′₁` from `A'` and `cc`, so far. -/
structure KC5 (p : Params) (STK : Nat) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (h : List (Vector Bool Spec.MlDsa.n)) (R : BitVec 32) (nz : Nat) (nc : Bool) (nr : Nat) (s : State) : Prop where
  vc : VC p STK σ s
  hh : hintOf p σ = some h
  hint : HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h
  a : ∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (aA p STK σ r s') (A' r s')
  z : ∀ i < p.ℓ, PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + i)))
    (if i < nz then zHat p (sgOf p σ) i else toRq (vZ p (sgOf p σ) i))
  c : PolyIs s.mem ((vlay p STK σ).A 0 (oP 15)) (if nc then ntt cc else cc)
  rows : ∀ r < nr, bytesAt s.mem ((vlay p STK σ).A 0 (oB + w1Len p * r)) (w1Len p) =
    simpleBitPack (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r) (w1Max p)
  r11 : s.gpr .r11 = R

/-- A part that writes `W` keeps what `KC5` says of the polynomials it does not write. -/
structure K5Chk (p : Params) (STK : Nat) (nr : Nat) (W : List (Nat × Nat × Nat)) : Prop where
  vc : vcChk p STK W = true
  hint : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true
  a : ∀ r < p.k, ∀ s' < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (20 + 8 * r + s'), 1024) W = true
  z : ∀ i < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true
  c : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 15, 1024) W = true
  rows : ∀ r < nr, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oB + w1Len p * r, w1Len p) W = true

/-- Proves a `K5Chk`, in each case of `w1Len`. -/
syntax "k5chk " term:max : tactic
macro_rules
  | `(tactic| k5chk $hF) => `(tactic| (
      rcases ($hF).w1l with hw1 | hw1 <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> vsep $hF [vcChk, hw1]))

theorem KC5.keep {p : Params} (hF : VFacts p) {STK : Nat} {σ : State} {A' : Nat → Nat → Spec.MlDsa.Poly}
    {cc : Spec.MlDsa.Poly} {h : List (Vector Bool Spec.MlDsa.n)} {R : BitVec 32} {nz : Nat} {nc : Bool} {nr : Nat}
    {s s' : State} (hk5 : KC5 p STK σ A' cc h R nz nc nr s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((vlay p STK σ).RL W) s s') (hc : K5Chk p STK nr W) : KC5 p STK σ A' cc h R nz nc nr s' := by
  have hL := hk5.vc.site.ok
  have hle : w1Len p ≤ 2 ^ 64 := by rcases hF.w1l with e | e <;> omega
  exact ⟨hk5.vc.keep hk hc.vc, hk5.hh, hintIs_keepW hL hk.frame hc.hint (by decide) (by have := hF.k; omega) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL hk.frame (hc.a r hr s' hs') (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => polyIs_keepW hL hk.frame (hc.z i hi) (by decide) rfl (hk5.z i hi),
    polyIs_keepW hL hk.frame hc.c (by decide) rfl hk5.c,
    fun r hr => by rw [bytes_keepW hL hk.frame (hc.rows r hr) (by decide) hle]; exact hk5.rows r hr,
    (hk.cs .r11 (by decide) (by decide)).trans hk5.r11⟩

/-- The states of `compute` with `nz`, `nc` and `nr`, for some `A'`, `cc`, `h` and `R`. -/
abbrev KX (p : Params) (STK : Nat) (nz : Nat) (nc : Bool) (nr : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, KC5 p STK σ A' cc h R nz nc nr s

/-! ## The NTTs of `z` and `c` -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

theorem nttZ_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A' cc h R} {s : State}
    (hk5 : KC5 p STK σ A' cc h R j false 0 s) : WP isa (nttAt P (pZ j)) s (KC5 p STK σ A' cc h R (j + 1) false 0) := by
  have hk := hF.k; have hl := hF.l
  have hs := hk5.vc.site
  have hL := hs.ok
  have hz := hk5.z j hj
  rw [ifn (Nat.lt_irrefl j)] at hz
  unfold nttAt
  refine ip_ok (t := ntt) hP.ntt hs (by omega) (f := pZ j) (w := sc oSS) ⟨rfl, by vsep hF⟩ ⟨rfl, by vsep hF⟩
    (show ix Reg.r7 ∈ vWb by decide) (show ix Reg.r7 ∈ vWb by decide) (by vsep hF) hz.1 fun s' k' hb => ?_
  refine ⟨hk5.vc.keep k' (by vsep hF [vcChk]), hk5.hh,
    hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => ?_, polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl hk5.c,
    fun _ h => absurd h (Nat.not_lt_zero _), (k'.cs .r11 (by decide) (by decide)).trans hk5.r11⟩
  by_cases e : i = j
  · subst e
    rw [ifp (Nat.lt_succ_self _)]
    show PolyIs s'.mem (lpa (vlay p STK σ) (pZ i)) _
    have e2 : polyAt s.mem (lpa (vlay p STK σ) (pZ i)) = _ := hz.2
    rw [e2] at hb
    exact hb
  · have := polyIs_keepW hL k'.frame (i := 0) (o := oP (8 + i)) (by vsep hF) (by decide) rfl (hk5.z i hi)
    by_cases hlt : i < j
    · rwa [ifp hlt, ← ifp (show i < j + 1 by omega) (zHat p (sgOf p σ) i) (toRq (vZ p (sgOf p σ) i))] at this
    · rwa [ifn hlt, ← ifn (show ¬ i < j + 1 by omega) (zHat p (sgOf p σ) i) (toRq (vZ p (sgOf p σ) i))] at this

theorem nttZ_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (KX p STK j false 0) (KX p STK (j + 1) false 0) (nttAt P (pZ j)) := by
  have hl := hF.l
  refine ⟨fun _ _ _ ⟨A', cc, h, R, hk5⟩ => WP.mono (nttZ_ok hP hF hS hj hk5) fun _ h' => ⟨A', cc, h, R, h'⟩, ?_⟩
  unfold nttAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    Reduced x.mem (lpa (vlay p STK σ) (pZ j)) ∧ Reduced y.mem (lpa (vlay p STK σ) (pZ j)))
    (RelCT.exists_ fun σ => ip_tr (t := ntt) hP.ntt (by omega) (f := pZ j) (w := sc oSS)
      (⟨rfl, by vsep hF⟩ : PtrIn (vlay p STK σ) (pZ j) 1024) ⟨rfl, by vsep hF⟩ (show ix Reg.r7 ∈ vWb by decide)
      (show ix Reg.r7 ∈ vWb by decide) (by vsep hF) fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
  have r₂ : Reduced _ (lpa (vlay p STK _) (pZ j)) := (h₂.z j hj).1
  rw [← vlay_pub pub] at r₂
  exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, (h₁.z j hj).1, r₂⟩

theorem nttC_ok {σ : State} {A' cc h R} {s : State} (hk5 : KC5 p STK σ A' cc h R p.ℓ false 0 s) :
    WP isa (nttAt P pC) s (KC5 p STK σ A' cc h R p.ℓ true 0) := by
  have hk := hF.k; have hl := hF.l
  have hs := hk5.vc.site
  have hL := hs.ok
  unfold nttAt
  refine ip_ok (t := ntt) hP.ntt hs (by omega) (f := pC) (w := sc oSS) ⟨rfl, by vsep hF⟩ ⟨rfl, by vsep hF⟩
    (show ix Reg.r7 ∈ vWb by decide) (show ix Reg.r7 ∈ vWb by decide) (by vsep hF) hk5.c.1 fun s' k' hb => ?_
  refine ⟨hk5.vc.keep k' (by vsep hF [vcChk]), hk5.hh,
    hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), (k'.cs .r11 (by decide) (by decide)).trans hk5.r11⟩
  show PolyIs s'.mem (lpa (vlay p STK σ) pC) _
  have e2 : polyAt s.mem (lpa (vlay p STK σ) pC) = cc := hk5.c.2
  rw [e2] at hb
  exact hb

theorem nttC_piece : VPiece p STK (KX p STK p.ℓ false 0) (KX p STK p.ℓ true 0) (nttAt P pC) := by
  refine ⟨fun _ _ _ ⟨A', cc, h, R, hk5⟩ => WP.mono (nttC_ok hP hF hS hk5) fun _ h' => ⟨A', cc, h, R, h'⟩, ?_⟩
  unfold nttAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    Reduced x.mem (lpa (vlay p STK σ) pC) ∧ Reduced y.mem (lpa (vlay p STK σ) pC))
    (RelCT.exists_ fun σ => ip_tr (t := ntt) hP.ntt (by omega) (f := pC) (w := sc oSS)
      (⟨rfl, by vsep hF⟩ : PtrIn (vlay p STK σ) pC 1024) ⟨rfl, by vsep hF⟩ (show ix Reg.r7 ∈ vWb by decide)
      (show ix Reg.r7 ∈ vWb by decide) (by vsep hF) fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
  have r₂ : Reduced _ (lpa (vlay p STK _) pC) := h₂.c.1
  rw [← vlay_pub pub] at r₂
  exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, h₁.c.1, r₂⟩

end

end VG.Proof.MlDsa.Arm.Verify
