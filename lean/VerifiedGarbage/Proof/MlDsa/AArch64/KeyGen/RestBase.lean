import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest

/-!
# ML-DSA key generation on AArch64: after the samplers

Untrusted: everything here is checked by Lean. Once the samplers are done,
with `Â` and `s₁ ‖ s₂` in memory as `A` and `S` and `x24` as `R` (`Good`),
the rest of the function computes the keys from them, whatever they are
(`KR`): after the copies of `ρ` and `K` (`copies_piece`), the first `np`
entries of `s₁ ‖ s₂` packed to `sk`, the first `nj` of `s₁` in the NTT
domain, and the first `nr` rows of `t` packed to `pk` and `sk`.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack)
open VG.Proof.MlDsa.KeyGen (t1K t0K Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A`, `S` and `R`, so far. -/
structure KR (p : Params) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (R : BitVec 64) (np nj nr : Nat)
    (s : State) : Prop where
  kc : KC p σ s
  x24 : s.gpr .x24 = R
  good : Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem (pa s (aP e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem (pa s (sP p (p.ℓ + i))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem (pa s (sP p j)) (if j < nj then ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem (pa s (.x26, 0)) 32 = rhoOf p σ
  sk0 : bytesAt s.mem (pa s (.x27, 0)) 32 = rhoOf p σ
  sk1 : bytesAt s.mem (pa s (.x27, 32)) 32 = kOf p σ
  packs : ∀ r < np, bytesAt s.mem (pa s (.x27, 128 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem (pa s (.x27, oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096

/-- A piece that writes `ws` keeps what `KR` says. -/
structure KRChk (p : Params) (np nj nr : Nat) (ws : List (Ptr × Nat)) : Prop where
  kc : kcChk p ws = true
  aS : ∀ e < p.k * p.ℓ, keepB kgR (kgW p) ws (aP e) 1024 = true
  s2 : ∀ i < p.k, keepB kgR (kgW p) ws (sP p (p.ℓ + i)) 1024 = true
  s1 : ∀ j < p.ℓ, keepB kgR (kgW p) ws (sP p j) 1024 = true
  pk0 : keepB kgR (kgW p) ws (.x26, 0) 32 = true
  sk0 : keepB kgR (kgW p) ws (.x27, 0) 32 = true
  sk1 : keepB kgR (kgW p) ws (.x27, 32) 32 = true
  packs : ∀ r < np, keepB kgR (kgW p) ws (.x27, 128 + lenS p * r) (lenS p) = true
  rows : ∀ i < nr, keepB kgR (kgW p) ws (.x26, 32 + 320 * i) 320 = true ∧
    keepB kgR (kgW p) ws (.x27, oT0 p + 416 * i) 416 = true

/-- Proves a `KRChk`, in each case of `η`. -/
syntax "krchk " term:max : tactic
macro_rules
  | `(tactic| krchk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr
      rcases ($hF).eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
      (try unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk) <;>
      lay [($hF).pk, ($hF).sk, hlen]))

theorem KR.keep {p : Params} (hF : PFacts p) {S' : Nat} {σ : State} (hp : kgPre p S' σ) {A : Nat → Poly}
    {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat} {s s' : State} (h : KR p σ A S R np nj nr s)
    {ws : List (Ptr × Nat)} (hP : PPostB S' s s' ws) (h24 : s'.gpr .x24 = s.gpr .x24) (hc : KRChk p np nj nr ws) :
    KR p σ A S R np nj nr s' := by
  have L := h.kc.lay hF hp
  exact ⟨h.kc.step hF hp hP hc.kc, h24.trans h.x24, h.good, h.small,
    fun e he => L.keepPoly hP (hc.aS e he) (h.aS e he), fun i hi => L.keepPoly hP (hc.s2 i hi) (h.s2 i hi),
    fun j hj => L.keepPoly hP (hc.s1 j hj) (h.s1 j hj), by rw [L.keepBytes hP hc.pk0]; exact h.pk0,
    by rw [L.keepBytes hP hc.sk0]; exact h.sk0, by rw [L.keepBytes hP hc.sk1]; exact h.sk1,
    fun r hr => by rw [L.keepBytes hP (hc.packs r hr)]; exact h.packs r hr,
    fun i hi => ⟨by rw [L.keepBytes hP (hc.rows i hi).1]; exact (h.rows i hi).1,
      by rw [L.keepBytes hP (hc.rows i hi).2]; exact (h.rows i hi).2⟩⟩

/-! ## `ρ` and `K` to the keys -/

/-- After the copies, for some `A`, `S` and `R`. -/
abbrev KR0 (p : Params) (σ s : State) : Prop := ∃ A S R, KR p σ A S R 0 0 0 s

theorem b26 (o n : Nat) : ∀ w ∈ [(((.x26, o) : Ptr), n)], w.1.1 ∈ bases := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; show Reg.x26 ∈ bases; decide

theorem b27 (o n : Nat) : ∀ w ∈ [(((.x27, o) : Ptr), n)], w.1.1 ∈ bases := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; show Reg.x27 ∈ bases; decide

theorem copies_ok {p : Params} (hF : PFacts p) {S' : Nat} {σ : State} (hp : kgPre p S' σ) {s : State}
    (h : KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) : WP isa (.block copies) s (KR0 p σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.k1.kc.lay hF hp
  unfold copies
  rw [WP.block_append_iff, WP.block_append_iff]
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  · refine WP.mono (copyP_ok L (dst := (.x26, 0)) (src := sc oHX) (by unfold copyChk; lay [hF.pk, hF.sk, hlen]))
      fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_
    have L₁ := L.post hP₁
    refine WP.mono (copyP_ok L₁ (dst := (.x27, 0)) (src := sc oHX) (by unfold copyChk; lay [hF.pk, hF.sk, hlen]))
      fun s₂ ⟨hP₂, k₂, hb₂⟩ => ?_
    have L₂ := L₁.post hP₂
    refine WP.mono (copyP_ok L₂ (dst := (.x27, 32)) (src := sc (oHX + 96))
      (by unfold copyChk; lay [hF.pk, hF.sk, hlen])) fun s₃ ⟨hP₃, k₃, hb₃⟩ => ?_
    have hP := PPostB.app (PPostB.app hP₁ hP₂ (b27 _ _)) hP₃ (b27 _ _)
    have h24 : s₃.gpr .x24 = s.gpr .x24 := by rw [k₃.get .x24, k₂.get .x24, k₁.get .x24]
    obtain ⟨A, S, hA, hS, hG⟩ := h.ex
    have hc : kcChk p ([((.x26, 0), 32)] ++ [((.x27, 0), 32)] ++ [((.x27, 32), 32)]) = true ∧
        (∀ e < p.k * p.ℓ, keepB kgR (kgW p) ([((.x26, 0), 32)] ++ [((.x27, 0), 32)] ++ [((.x27, 32), 32)])
          (aP e) 1024 = true) ∧
        (∀ r < p.ℓ + p.k, keepB kgR (kgW p) ([((.x26, 0), 32)] ++ [((.x27, 0), 32)] ++ [((.x27, 32), 32)])
          (sP p r) 1024 = true) :=
      ⟨by unfold kcChk; lay [hF.pk, hF.sk, hlen], fun _ _ => by lay [hF.pk, hF.sk, hlen],
        fun _ _ => by lay [hF.pk, hF.sk, hlen]⟩
    have hHX₁ : bytesAt s₁.mem (pa s₁ (sc oHX)) 128 = hxOf p σ := by
      rw [L.keepBytes hP₁ (by lay [hF.pk])]; exact h.k1.hx
    have hHX₂ : bytesAt s₂.mem (pa s₂ (sc oHX)) 128 = hxOf p σ := by
      rw [L₁.keepBytes hP₂ (by lay [hF.pk, hF.sk, hlen])]; exact hHX₁
    have e1 : bytesAt s.mem (pa s (sc oHX)) 32 = rhoOf p σ := by
      rw [rho_eq, ← h.k1.hx, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
    have e1' : bytesAt s₁.mem (pa s₁ (sc oHX)) 32 = rhoOf p σ := by
      rw [rho_eq, ← hHX₁, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
    have e2 : bytesAt s₂.mem (pa s₂ (sc (oHX + 96))) 32 = kOf p σ := by
      rw [kOf_eq, ← hHX₂, Proof.MlKem.bytesAt_slice _ _ (show 96 + 32 ≤ 128 by decide), sc_add]
    refine ⟨A, S, s.gpr .x24, ⟨h.k1.kc.step hF hp hP hc.1, h24, hG, fun r hr => (hS r hr).2,
      fun e he => L.keepPoly hP (hc.2.1 e he) (hA e he),
      fun i hi => L.keepPoly hP (hc.2.2 _ (by omega)) (hS (p.ℓ + i) (by omega)).1,
      fun j hj => by rw [ifn (Nat.not_lt_zero j)]; exact L.keepPoly hP (hc.2.2 j (by omega)) (hS j (by omega)).1,
      ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    · rw [L₂.keepBytes hP₃ (by lay [hF.pk, hF.sk, hlen]), L₁.keepBytes hP₂ (by lay [hF.pk, hF.sk, hlen]),
        hP₁.pa (show Reg.x26 ∈ bases by decide), hb₁, e1]
    · rw [L₂.keepBytes hP₃ (by lay [hF.pk, hF.sk, hlen]), hP₂.pa (show Reg.x27 ∈ bases by decide), hb₂, e1']
    · rw [hP₃.pa (show Reg.x27 ∈ bases by decide), hb₃, e2]

theorem copies_piece {p : Params} (hF : PFacts p) {S : Nat} :
    Piece p S (fun σ s => KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KR0 p) (.block copies) :=
  ⟨fun _ _ hp h => copies_ok hF hp h,
    rel_of (Q := Two p S) (taintRel [.x25, .x26, .x27, .x28] (fun x y h => h.bases) (by taint_decide))
      fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc⟩

end VG.Proof.MlDsa.AArch64.KeyGen
