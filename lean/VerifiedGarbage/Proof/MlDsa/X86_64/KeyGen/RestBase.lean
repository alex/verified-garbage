import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Samp4
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest

/-!
# ML-DSA key generation on x86-64: after the samplers

Untrusted: everything here is checked by Lean. Once the samplers are done,
with `Â` and `s₁ ‖ s₂` in memory as `A` and `S` and `r15` as `R` (`Good`),
the rest of the function computes the keys from them, whatever they are
(`KR`): after the copies of `ρ` and `K` (`copies_piece`), the first `np`
entries of `s₁ ‖ s₂` packed to `sk`, the first `nj` of `s₁` in the NTT
domain, and the first `nr` rows of `t` packed to `pk` and `sk`.
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc copy seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack)
open VG.Proof.MlDsa.KeyGen (t1K t0K)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A`, `S` and `R`, so far. -/
structure KR (p : Params) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (R : BitVec 64) (np nj nr : Nat)
    (s : State) : Prop where
  kc : KC p σ s
  r15 : s.gpr .r15 = R
  good : Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem (pa s (aP e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem (pa s (sP p (p.ℓ + i))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem (pa s (sP p j)) (if j < nj then ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem (pa s (.r12, 0)) 32 = rhoOf p σ
  sk0 : bytesAt s.mem (pa s (.r13, 0)) 32 = rhoOf p σ
  sk1 : bytesAt s.mem (pa s (.r13, 32)) 32 = kOf p σ
  packs : ∀ r < np, bytesAt s.mem (pa s (.r13, 128 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem (pa s (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem (pa s (.r13, oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096

/-- A piece that writes `ws` keeps what `KR` says. -/
structure KRChk (p : Params) (np nj nr : Nat) (ws : List (Ptr × Nat)) : Prop where
  kc : kcChk p ws = true
  aS : ∀ e < p.k * p.ℓ, keepB (kgB p) ws (aP e) 1024 = true
  s2 : ∀ i < p.k, keepB (kgB p) ws (sP p (p.ℓ + i)) 1024 = true
  s1 : ∀ j < p.ℓ, keepB (kgB p) ws (sP p j) 1024 = true
  pk0 : keepB (kgB p) ws (.r12, 0) 32 = true
  sk0 : keepB (kgB p) ws (.r13, 0) 32 = true
  sk1 : keepB (kgB p) ws (.r13, 32) 32 = true
  packs : ∀ r < np, keepB (kgB p) ws (.r13, 128 + lenS p * r) (lenS p) = true
  rows : ∀ i < nr, keepB (kgB p) ws (.r12, 32 + 320 * i) 320 = true ∧ keepB (kgB p) ws (.r13, oT0 p + 416 * i) 416 = true

/-- Proves a `KRChk`, in each case of `η`. -/
syntax "krchk " term:max : tactic
macro_rules
  | `(tactic| krchk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl
      rcases ($hF).eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
      layk [($hF).pk, ($hF).sk, hlen]))

theorem KR.keep {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 64} {np nj nr : Nat} {s s' : State} (h : KR p σ A S R np nj nr s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hx : MX s' = MX s) (h15 : s'.gpr .r15 = s.gpr .r15) (hc : KRChk p np nj nr ws) :
    KR p σ A S R np nj nr s' := by
  have L := h.kc.lay hF hp
  exact ⟨h.kc.step hF hp hP hx hc.kc, h15.trans h.r15, h.good, h.small,
    fun e he => polyIs_frame' L hP (hc.aS e he) (h.aS e he), fun i hi => polyIs_frame' L hP (hc.s2 i hi) (h.s2 i hi),
    fun j hj => polyIs_frame' L hP (hc.s1 j hj) (h.s1 j hj), by rw [L.keepBytes hP hc.pk0]; exact h.pk0,
    by rw [L.keepBytes hP hc.sk0]; exact h.sk0, by rw [L.keepBytes hP hc.sk1]; exact h.sk1,
    fun r hr => by rw [L.keepBytes hP (hc.packs r hr)]; exact h.packs r hr,
    fun i hi => ⟨by rw [L.keepBytes hP (hc.rows i hi).1]; exact (h.rows i hi).1,
      by rw [L.keepBytes hP (hc.rows i hi).2]; exact (h.rows i hi).2⟩⟩

/-! ## `ρ` and `K` to the keys -/

theorem r12_bases (o n : Nat) : ∀ w ∈ [(((.r12, o) : Ptr), n)], w.1.1 ∈ bases := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; show Reg.r12 ∈ bases; decide

theorem r13_bases (o n : Nat) : ∀ w ∈ [(((.r13, o) : Ptr), n)], w.1.1 ∈ bases := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; show Reg.r13 ∈ bases; decide

/-- After the copies, for some `A`, `S` and `R`. -/
abbrev KR0 (p : Params) (σ s : State) : Prop := ∃ A S R, KR p σ A S R 0 0 0 s

theorem copies_ok {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {s : State}
    (h : KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) : WP isa copies s (KR0 p σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have L := h.k1.kc.lay hF hp
  unfold copies
  refine WP.seq (WP.mono (copy_okM L (dst := (.r12, 0)) (src := sc oHX) (n := 32) (by decide)
    (by layk [hF.pk, hF.sk])) fun s₁ ⟨⟨hP₁, hb₁⟩, hx₁⟩ => ?_)
  have L₁ := L.post hP₁.b (kgB_bases p)
  refine WP.seq (WP.mono (copy_okM L₁ (dst := (.r13, 0)) (src := sc oHX) (n := 32) (by decide)
    (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> layk [hF.pk, hF.sk, hlen])) fun s₂ ⟨⟨hP₂, hb₂⟩, hx₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b (kgB_bases p)
  refine WP.mono (copy_okM L₂ (dst := (.r13, 32)) (src := sc (oHX + 96)) (n := 32) (by decide)
    (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> layk [hF.pk, hF.sk, hlen])) fun s₃ ⟨⟨hP₃, hb₃⟩, hx₃⟩ => ?_
  have hP := PPostB.app (PPostB.app hP₁.b hP₂.b (r13_bases _ _)) hP₃.b (r13_bases _ _)
  have hx : MX s₃ = MX s := hx₃.trans (hx₂.trans hx₁)
  have h15 : s₃.gpr .r15 = s.gpr .r15 := by
    rw [hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide)]
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  have hc : kcChk p ([((.r12, 0), 32)] ++ [((.r13, 0), 32)] ++ [((.r13, 32), 32)]) = true ∧
      (∀ e < p.k * p.ℓ, keepB (kgB p) ([((.r12, 0), 32)] ++ [((.r13, 0), 32)] ++ [((.r13, 32), 32)]) (aP e) 1024 = true) ∧
      (∀ r < p.ℓ + p.k, keepB (kgB p) ([((.r12, 0), 32)] ++ [((.r13, 0), 32)] ++ [((.r13, 32), 32)]) (sP p r) 1024
        = true) := by
    rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
    exact ⟨by layk [hF.pk, hF.sk, hlen], fun _ _ => by layk [hF.pk, hF.sk, hlen],
      fun _ _ => by layk [hF.pk, hF.sk, hlen]⟩
  -- The bytes of `HX`, and `ρ`, `K`.
  have hHX₁ : bytesAt s₁.mem (pa s₁ (sc oHX)) 128 = hxOf p σ := by rw [L.keepBytes hP₁.b (by layk [hF.pk])]; exact h.k1.hx
  have hHX₂ : bytesAt s₂.mem (pa s₂ (sc oHX)) 128 = hxOf p σ := by
    rw [L₁.keepBytes hP₂.b (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> layk [hF.pk, hF.sk, hlen])]; exact hHX₁
  have e1 : bytesAt s.mem (pa s (sc oHX)) 32 = rhoOf p σ := by
    rw [rho_eq, ← h.k1.hx, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  have e1' : bytesAt s₁.mem (pa s₁ (sc oHX)) 32 = rhoOf p σ := by
    rw [rho_eq, ← hHX₁, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  have e2 : bytesAt s₂.mem (pa s₂ (sc (oHX + 96))) 32 = kOf p σ := by
    rw [kOf_eq, ← hHX₂, Proof.MlKem.bytesAt_slice _ _ (show 96 + 32 ≤ 128 by decide), pa, pa, off_add]
  refine ⟨A, S, s.gpr .r15, ⟨h.k1.kc.step hF hp hP hx hc.1, h15, hG, fun r hr => (hS r hr).2,
    fun e he => polyIs_frame' L hP (hc.2.1 e he) (hA e he),
    fun i hi => polyIs_frame' L hP (hc.2.2 _ (by omega)) (hS (p.ℓ + i) (by omega)).1,
    fun j hj => by rw [ifn (Nat.not_lt_zero j)]; exact polyIs_frame' L hP (hc.2.2 j (by omega)) (hS j (by omega)).1,
    ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  · rw [L₂.keepBytes hP₃.b (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> layk [hF.pk, hF.sk, hlen]),
      L₁.keepBytes hP₂.b (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> layk [hF.pk, hF.sk, hlen]),
      hP₁.pa (by decide), hb₁, e1]
  · rw [L₂.keepBytes hP₃.b (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> layk [hF.pk, hF.sk, hlen]),
      hP₂.pa (by decide), hb₂, e1']
  · rw [hP₃.pa (by decide), hb₃, e2]

theorem copies_piece {p : Params} (hF : PFacts p) :
    Piece p (fun σ s => KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KR0 p) copies :=
  ⟨fun _ _ hp h => copies_ok hF hp h,
    rel_of (Q := Two p) (taintRel [.rbx, .r12, .r13] (fun x y h r hr => h.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)) (by taint_decide))
      fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc⟩

end VG.Proof.MlDsa.X86_64.KeyGen
