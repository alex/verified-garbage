import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest

/-!
# ML-DSA key generation on 32-bit ARM: after the samplers

Once the samplers are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S`
and `r11` as `R` (`Good`), the rest of the function computes the keys from
them, whatever they are (`KR`): after the copies of `ρ` and `K`
(`copies_piece`), the first `np` entries of `s₁ ‖ s₂` packed to `sk`, the
first `nj` of `s₁` in the NTT domain, and the first `nr` rows of `t` packed to
`pk` and `sk`.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (copy)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack)
open VG.Proof.MlDsa.KeyGen (t1K t0K Small Good ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A`, `S` and `R`, so far. -/
structure KR (p : Params) (STK : Nat) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (R : BitVec 32)
    (np nj nr : Nat) (s : State) : Prop where
  kc : KC p STK σ s
  r11 : s.gpr .r11 = R
  good : Good p (xiOf σ) (p.k * p.ℓ) (p.ℓ + p.k) A S R
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem ((lay p STK σ).A 0 (oP e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + (p.ℓ + i)))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))
    (if j < nj then ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem ((lay p STK σ).A 3 0) 32 = rhoOf p σ
  sk0 : bytesAt s.mem ((lay p STK σ).A 4 0) 32 = rhoOf p σ
  sk1 : bytesAt s.mem ((lay p STK σ).A 4 32) 32 = kOf p σ
  packs : ∀ r < np, bytesAt s.mem ((lay p STK σ).A 4 (128 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem ((lay p STK σ).A 3 (32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem ((lay p STK σ).A 4 (oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096

/-- A part that writes `W` keeps what `KR` says. -/
structure KRChk (p : Params) (STK : Nat) (np nj nr : Nat) (W : List (Nat × Nat × Nat)) : Prop where
  kc : kcChk p STK W = true
  aS : ∀ e < p.k * p.ℓ, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP e, 1024) W = true
  s2 : ∀ i < p.k, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + (p.ℓ + i)), 1024) W = true
  s1 : ∀ j < p.ℓ, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + j), 1024) W = true
  pk0 : sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (3, 0, 32) W = true
  sk0 : sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, 0, 32) W = true
  sk1 : sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, 32, 32) W = true
  packs : ∀ r < np, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, 128 + lenS p * r, lenS p) W = true
  rows : ∀ i < nr, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (3, 32 + 320 * i, 320) W = true ∧
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, oT0 p + 416 * i, 416) W = true

/-- Proves a `KRChk`, in each case of `η`. -/
syntax "krchk " term:max : tactic
macro_rules
  | `(tactic| krchk $hF) => `(tactic| (
      rcases ($hF).eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
      lsep $hF [kcChk, ($hF).pk, ($hF).sk, hlen]))

theorem KR.keep {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nj nr : Nat} {s s' : State} (h : KR p STK σ A S R np nj nr s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((lay p STK σ).RL W) s s') (hc : KRChk p STK np nj nr W) : KR p STK σ A S R np nj nr s' := by
  have hL := h.kc.site.ok
  have hle : lenS p ≤ 2 ^ 64 := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have kb : ∀ {i o l : Nat}, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (i, o, l) W = true → i ∈ kWb →
      l ≤ 2 ^ 64 → bytesAt s'.mem ((lay p STK σ).A i o) l = bytesAt s.mem ((lay p STK σ).A i o) l :=
    fun hs hi hl => bytes_keepW hL hk.frame hs hi hl
  exact ⟨h.kc.keep hk hc.kc, (hk.cs .r11 (by decide) (by decide)).trans h.r11, h.good, h.small,
    fun e he => polyIs_keepW hL hk.frame (hc.aS e he) (by decide) rfl (h.aS e he),
    fun i hi => polyIs_keepW hL hk.frame (hc.s2 i hi) (by decide) rfl (h.s2 i hi),
    fun j hj => polyIs_keepW hL hk.frame (hc.s1 j hj) (by decide) rfl (h.s1 j hj),
    by rw [kb hc.pk0 (by decide) (by decide)]; exact h.pk0,
    by rw [kb hc.sk0 (by decide) (by decide)]; exact h.sk0,
    by rw [kb hc.sk1 (by decide) (by decide)]; exact h.sk1,
    fun r hr => by
      rw [kb (hc.packs r hr) (by decide) hle]
      exact h.packs r hr,
    fun i hi => ⟨by rw [kb (hc.rows i hi).1 (by decide) (by decide)]; exact (h.rows i hi).1,
      by rw [kb (hc.rows i hi).2 (by decide) (by decide)]; exact (h.rows i hi).2⟩⟩

/-! ## `ρ` and `K` to the keys -/

/-- After the copies, for some `A`, `S` and `R`. -/
abbrev KR0 (p : Params) (STK : Nat) (σ s : State) : Prop := ∃ A S R, KR p STK σ A S R 0 0 0 s

theorem copies_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State}
    (h : KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) : WP isa copies s (KR0 p STK σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.k1.kc.site
  unfold copies
  refine WP.seq (WP.mono (copyS hs (sb := .r7) (so := oHX) (db := .r5) (dO := 0) (len := 32) ⟨rfl, by lsep hF⟩
    ⟨rfl, by lsep hF [hF.pk]⟩ (show ix Reg.r5 ∈ kWb by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by lsep hF [hF.pk])) fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h.keep k₁ (by lsep hF [k1Chk, kcChk, hF.pk]) (fun e' he' => by lsep hF [hF.pk])
    (fun r' hr' => by lsep hF [hF.pk]) (k₁.cs .r11 (by decide) (by decide))
  refine WP.seq (WP.mono (copyS h₁.k1.kc.site (sb := .r7) (so := oHX) (db := .r6) (dO := 0) (len := 32)
    ⟨rfl, by lsep hF⟩ ⟨rfl, by lsep hF [hF.sk]⟩ (show ix Reg.r6 ∈ kWb by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by lsep hF [hF.sk])) fun s₂ ⟨k₂, b₂⟩ => ?_)
  have h₂ := h₁.keep k₂ (by lsep hF [k1Chk, kcChk, hF.sk]) (fun e' he' => by lsep hF [hF.sk])
    (fun r' hr' => by lsep hF [hF.sk]) (k₂.cs .r11 (by decide) (by decide))
  refine WP.mono (copyS h₂.k1.kc.site (sb := .r7) (so := oHX + 96) (db := .r6) (dO := 32) (len := 32)
    ⟨rfl, by lsep hF⟩ ⟨rfl, by lsep hF [hF.sk]⟩ (show ix Reg.r6 ∈ kWb by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by lsep hF [hF.sk])) fun s₃ ⟨k₃, b₃⟩ => ?_
  have h₃ := h₂.keep k₃ (by lsep hF [k1Chk, kcChk, hF.sk]) (fun e' he' => by lsep hF [hF.sk])
    (fun r' hr' => by lsep hF [hF.sk]) (k₃.cs .r11 (by decide) (by decide))
  have hL := hs.ok
  obtain ⟨A, S, hA, hS, hG⟩ := h₃.ex
  have e1 : ∀ {m : Mem}, bytesAt m ((lay p STK σ).A 0 oHX) 128 = hxOf p σ →
      bytesAt m ((lay p STK σ).A 0 oHX) 32 = rhoOf p σ := fun hx => by
    rw [rho_eq, ← hx, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  refine ⟨A, S, s₃.gpr .r11, ⟨h₃.k1.kc, rfl, hG, fun r hr => (hS r hr).2, hA,
    fun i hi => (hS (p.ℓ + i) (by omega)).1,
    fun j hj => by rw [ifn (Nat.not_lt_zero j)]; exact (hS j (by omega)).1, ?_, ?_, ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  · rw [bytes_keepW hL k₃.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk, hF.sk]) (by decide) (by decide),
      bytes_keepW hL k₂.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk, hF.sk]) (by decide) (by decide)]
    exact b₁.trans (e1 h.k1.hx)
  · rw [bytes_keepW hL k₃.frame (i := 4) (o := 0) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
    exact b₂.trans (e1 h₁.k1.hx)
  · show bytesAt s₃.mem (lpa (lay p STK σ) (.r6, 32)) 32 = _
    rw [b₃, kOf_eq, ← h₂.k1.hx, Proof.MlKem.bytesAt_slice _ _ (show 96 + 32 ≤ 128 by decide), add_ofNat_add]
    rfl

/-- Two runs in every layout of key generation, from the taint analysis of
the pointers of the layout. -/
theorem ktaint4 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7]) c hc).isSome = true) :
    RelCT isa (KTwo p STK) c fun _ _ => True :=
  ktwo fun _ => taint4 (fun _ _ h => h) h

theorem copies_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KR0 p STK) copies :=
  ⟨fun _ _ _ h => copies_ok hF h,
    rel_of (ktaint4 (by taint_decide)) fun _ _ _ _ _ _ pub h₁ h₂ => kc_two pub h₁.k1.kc h₂.k1.kc⟩

end VG.Proof.MlDsa.Arm.KeyGen
