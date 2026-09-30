import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds

/-!
# ML-DSA key generation on x86 (32-bit): the samplers

Untrusted: everything here is checked by Lean. Each entry of `Â` (`expA_piece`)
and of `s₁ ‖ s₂` (`expS_piece`): its seed set, the sampler called, its result
ANDed into `oACC` and the polynomial masked with it (`maskA`), which keeps
`KSamp` for one more entry.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly keyGenInternal toRq polyAt
  coeffAt Reduced PolyIs integerToBytes)
open VG.Proof.MlDsa.KeyGen (seedA seedS bmax)
open VG.Spec.Sha3 (bytesAt)

/-- The taint check of the mask is the same for every polynomial. -/
theorem maskA_tt (po : Nat) : (VG.X86.taint.check (τr [.esi]) (maskA oACC po)
    (VG.Taint.hintOf VG.X86.taint (τr [.esi]) (maskA oACC 0))).isSome = true := by
  kernel_rfl

theorem ifp {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a := ite_eq_left_iff.mpr fun h' => absurd h h'
theorem ifn {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b := ite_eq_right_iff.mpr fun h' => absurd h' h

/-! ## An entry of `Â` -/

theorem seedA_eq (ρ : List Byte) (r s : Nat) :
    seedA ρ r s = ρ ++ ([BitVec.ofNat 8 s] ++ [BitVec.ofNat 8 r]) := by
  simp only [seedA, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]

/-! ## An entry of `s₁ ‖ s₂` -/

theorem seedS_eq (ρ' : List Byte) {r : Nat} (hr : r < 256) :
    seedS ρ' r = ρ' ++ ([BitVec.ofNat 8 r] ++ [0]) := by
  simp only [seedS, Proof.MlDsa.KeyGen.integerToBytes_two hr]; rfl

theorem eta_of {p : Params} (hF : PFacts p) : p.η = 2 ∨ p.η = 4 := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p)
include hP hF

/-- Before the call of `RejNTTPoly` for entry `e`. -/
structure SA2 (p : Params) (e : Nat) (s₀ s : State) : Prop extends KSamp p e 0 s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (sb oSA 34)) 34 = seedA (rhoOf p s₀) (e / p.ℓ) (e % p.ℓ)

/-- After it. -/
structure SA3 (p : Params) (e : Nat) (s₀ s : State) : Prop where
  kb : KB p s₀ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (Buf.addr s₀ (aB e')) (A e')) ∧
    Good p s₀ e 0 A S (accV s₀ s)
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (aB e))
  out : Spec.MlDsa.Outcome (fun b => rejNTTPoly b.rejNTT (seedA (rhoOf p s₀) (e / p.ℓ) (e % p.ℓ))) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (aB e)))

theorem expA_piece {e : Nat} (he : e < p.k * p.ℓ) : KP p (KSamp p e 0) (KSamp p (e + 1) 0) (expA P p e) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  unfold expA
  refine Piece.seq (B := fun s₀ s => KSamp p e 0 s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (sb (oSA + 32) 1)) 1 = [BitVec.ofNat 8 (e % p.ℓ)])
    (st8_piece (Y := YK p) (oSA + 32) (e % p.ℓ) (by layp hF) (ht := .block []) (by kernel_rfl)
      (fun _ _ _ h => h.kb.ctx) fun s₀ s s' hp h h' m' =>
        ⟨h.keep hp (N := 0) (by omega) ⟨by layp hF [safeKB], by layp hF, fun _ _ => by layp hF, fun _ h => absurd h (by omega)⟩
          (m' ▸ frW8) h', by rw [m', YK_sc]; exact st8_bytes _ _ _ _ _⟩) ?_
  refine Piece.seq (B := SA2 p e)
    (st8_piece (Y := YK p) (oSA + 33) (e / p.ℓ) (by layp hF) (ht := .block []) (by kernel_rfl)
      (fun _ _ _ h => h.1.kb.ctx) fun s₀ s s' hp h h' m' =>
        ⟨h.1.keep hp (N := 0) (by omega) ⟨by layp hF [safeKB], by layp hF, fun _ _ => by layp hF,
          fun _ h => absurd h (by omega)⟩ (m' ▸ frW8) h', ?_⟩) ?_
  · have k32 := keepBytes hp (N := 0) (stkN (by omega)) (b := sb oSA 32) (by layp hF) (m' ▸ frW8)
    have k1 := keepBytes hp (N := 0) (stkN (by omega)) (b := sb (oSA + 32) 1) (by layp hF) (m' ▸ frW8)
    rw [show (34 : Nat) = 32 + (1 + 1) from rfl, bytes_cat hp _ (l₁ := 32) (by layp hF) (by layp hF),
      bytes_cat hp _ (l₁ := 1) (l₂ := 1) (by layp hF) (by layp hF), k32, k1, h.1.kb.sa, h.2, seedA_eq, m', YK_sc,
      st8_bytes]
  refine Piece.seq (B := SA3 p e) (rejNtt_piece (Y := YK p) hP.rejNtt kS oSA kS (oP e) kS oSS (by layp hF)
    (Nat.le_of_eq (YK_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.kb.ctx)
    (fun s₀ s₀' s s' _ _ hq h h' => by rw [h.seed, h'.seed, (TPub.leak hq).1])
    fun s₀ s s' hp h h' fr red out => ?_) ?_
  · obtain ⟨A, S, hA, -, hG⟩ := h.ex
    have sf : SafeS p e 0 [aB e, ssB 2048] := ⟨by layp hF [safeKB], by layp hF, fun _ _ => by layp hF,
      fun _ h => absurd h (by omega)⟩
    refine ⟨h.kb.keep hp (N := 80) (by omega) sf.kb fr h', ⟨A, S, fun e' he' => keepPolyD hp (stkN (by omega))
      (sf.a e' he') fr (hA e' he'), ?_⟩, red, ?_⟩
    · rw [acc_keep hp (N := 80) (by omega) sf.acc fr]; exact hG
    · rw [← h.seed]; exact out
  refine maskA_piece (Y := YK p) oACC (oP e) (by layp hF) (maskA_tt _) (fun _ _ _ h => h.kb.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_
  simp only [YK_sc] at fr ha hc
  obtain ⟨A, S, hA, hG⟩ := h.ex
  have r01 : s.gpr .eax = 0 ∨ s.gpr .eax = 1 := by
    rcases h.out with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨m1, m0⟩ := Proof.MlDsa.KeyGen.masked r01 hc
  obtain ⟨a01, aiff⟩ := Proof.MlDsa.KeyGen.acc_and (good_01 hG) r01
  have fr' := fr2 fr
  have sk : safeKB p [sb oACC 4, aB e] = true := by layp hF [safeKB]
  have sa : ∀ e' < e, (YK p).apart (aB e') [sb oACC 4, aB e] = true := fun _ _ => by layp hF
  refine ⟨h.kb.keep hp (N := 0) (by omega) sk fr' h', fun e' => if e' = e then polyAt s'.mem (Buf.addr s₀ (aB e))
    else A e', S, fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega)]
      exact keepPolyD hp (stkN (by omega)) (sa e' he') fr' (hA e' he')
    · rw [ifp rfl]
      refine ⟨?_, rfl⟩
      rcases r01 with e0 | e1
      · exact (m0 e0).1
      · exact (m1 e1).2.2 (h.red e1)
  · have ea : accV s₀ s' = accV s₀ s &&& s.gpr .eax := ha
    rw [ea]
    rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
    · rcases h.out with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨aiff.mpr ⟨h1, ho⟩, bmax b b', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        dsimp only
        rcases (by omega : e' < e + 1 → e' < e ∨ e' = e) he' with he' | rfl
        · rw [ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hb e' he')
        · rw [ifp rfl, (m1 ho).2.1]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejNTT hb'
      · rw [ho, h1]
        exact .inr ⟨by decide, Proof.MlDsa.KeyGen.keyGenInternal_none_A hq hr hn⟩
    · rw [h0]
      exact .inr ⟨BitVec.zero_and, hn⟩


/-- Before the call of `RejBoundedPoly` for entry `r`. -/
structure SS2 (p : Params) (r : Nat) (s₀ s : State) : Prop extends KSamp p (p.k * p.ℓ) r s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (sb oSB 66)) 66 = seedS (rho'Of p s₀) r

/-- After it. -/
structure SS3 (p : Params) (r : Nat) (s₀ s : State) : Prop where
  kb : KB p s₀ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < p.k * p.ℓ, PolyIs s.mem (Buf.addr s₀ (aB e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (Buf.addr s₀ (sB p r')) (toRq (S r')) ∧ Small p.η (S r')) ∧
    Good p s₀ (p.k * p.ℓ) r A S (accV s₀ s)
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (sB p r))
  out : Spec.MlDsa.Outcome (fun b => (rejBoundedPoly p.η b.rejBounded (seedS (rho'Of p s₀) r)).map toRq)
    (s.gpr .eax) (polyAt s.mem (Buf.addr s₀ (sB p r)))

theorem expS_piece {r : Nat} (hr : r < p.ℓ + p.k) :
    KP p (KSamp p (p.k * p.ℓ) r) (KSamp p (p.k * p.ℓ) (r + 1)) (expS P p r) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hr256 : r < 256 := by omega
  unfold expS
  refine Piece.seq (B := SS2 p r)
    (st8_piece (Y := YK p) (oSB + 64) r (by layp hF) (ht := .block []) (by kernel_rfl)
      (fun _ _ _ h => h.kb.ctx) fun s₀ s s' hp h h' m' =>
        ⟨h.keep hp (N := 0) (by omega) ⟨by layp hF [safeKB], by layp hF, fun _ _ => by layp hF,
          fun _ _ => by layp hF⟩ (m' ▸ frW8) h', ?_⟩) ?_
  · have k64 := keepBytes hp (N := 0) (stkN (by omega)) (b := sb oSB 64) (by layp hF) (m' ▸ frW8)
    have k65 := keepBytes hp (N := 0) (stkN (by omega)) (b := sb (oSB + 65) 1) (by layp hF) (m' ▸ frW8)
    rw [show (66 : Nat) = 64 + (1 + 1) from rfl, bytes_cat hp _ (l₁ := 64) (by layp hF) (by layp hF),
      bytes_cat hp _ (l₁ := 1) (l₂ := 1) (by layp hF) (by layp hF), k64, show oSB + 64 + 1 = oSB + 65 from rfl, k65,
      h.kb.sbb, h.kb.z, seedS_eq _ hr256, m', YK_sc, st8_bytes]
  refine Piece.seq (B := SS3 p r) (rejBounded_piece (Y := YK p) hP.rejBounded kS oSB p.η kS (oP (p.k * p.ℓ + r))
    kS oSS (eta_of hF) (by layp hF) (Nat.le_of_eq (YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => h.kb.ctx) (fun s₀ s₀' s s' _ _ hq h h' => by rw [h.seed, h'.seed, (TPub.leak hq).2 r hr])
    fun s₀ s s' hp h h' fr red out => ?_) ?_
  · obtain ⟨A, S, hA, hS, hG⟩ := h.ex
    have sf : SafeS p (p.k * p.ℓ) r [sB p r, ssB 2048] := ⟨by layp hF [safeKB], by layp hF, fun _ _ => by layp hF,
      fun _ _ => by layp hF⟩
    refine ⟨h.kb.keep hp (N := 80) (by omega) sf.kb fr h', ⟨A, S, fun e' he' => keepPolyD hp (stkN (by omega))
      (sf.a e' he') fr (hA e' he'), fun r' hr' => ⟨keepPolyD hp (stkN (by omega)) (sf.s r' hr') fr (hS r' hr').1,
        (hS r' hr').2⟩, ?_⟩, red, ?_⟩
    · rw [acc_keep hp (N := 80) (by omega) sf.acc fr]; exact hG
    · rw [← h.seed]; exact out
  refine maskA_piece (Y := YK p) oACC (oP (p.k * p.ℓ + r)) (by layp hF) (maskA_tt _) (fun _ _ _ h => h.kb.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_
  simp only [YK_sc] at fr ha hc
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  have r01 : s.gpr .eax = 0 ∨ s.gpr .eax = 1 := by
    rcases h.out with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨m1, m0⟩ := Proof.MlDsa.KeyGen.masked r01 hc
  obtain ⟨a01, aiff⟩ := Proof.MlDsa.KeyGen.acc_and (good_01 hG) r01
  have fr' := fr2 fr
  have sk : safeKB p [sb oACC 4, sB p r] = true := by layp hF [safeKB]
  have sa : ∀ e' < p.k * p.ℓ, (YK p).apart (aB e') [sb oACC 4, sB p r] = true := fun _ _ => by layp hF
  have ss : ∀ r' < r, (YK p).apart (sB p r') [sb oACC 4, sB p r] = true := fun _ _ => by layp hF
  have kA : ∀ e' < p.k * p.ℓ, PolyIs s'.mem (Buf.addr s₀ (aB e')) (A e') := fun e' he' =>
    keepPolyD hp (stkN (by omega)) (sa e' he') fr' (hA e' he')
  have kS' : ∀ r' < r, PolyIs s'.mem (Buf.addr s₀ (sB p r')) (toRq (S r')) ∧ Small p.η (S r') := fun r' hr' =>
    ⟨keepPolyD hp (stkN (by omega)) (ss r' hr') fr' (hS r' hr').1, (hS r' hr').2⟩
  have ea : accV s₀ s' = accV s₀ s &&& s.gpr .eax := ha
  rcases r01 with e0 | e1
  · -- The sampler failed: the polynomial is zero.
    have hn : rejBoundedPoly p.η minBounds.rejBounded (seedS (rho'Of p s₀) r) = none := by
      rcases h.out with ⟨h, _⟩ | ⟨_, h⟩
      · rw [e0] at h; exact absurd h (by decide)
      · exact Option.map_eq_none_iff.mp h
    refine ⟨h.kb.keep hp (N := 0) (by omega) sk fr' h', A, fun r' => if r' = r then Proof.MlDsa.KeyGen.zeroI
      else S r', kA, fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [ifn (by omega)]; exact kS' r' hr'
      · rw [ifp rfl]; exact ⟨(m0 e0), Proof.MlDsa.KeyGen.small_zero _⟩
    · rw [ea, e0]
      exact .inr ⟨BitVec.and_zero, Proof.MlDsa.KeyGen.keyGenInternal_none_S hr hn⟩
  · -- It succeeded.
    obtain ⟨b', hb'⟩ : ∃ b' : Bounds, (rejBoundedPoly p.η b'.rejBounded (seedS (rho'Of p s₀) r)).map toRq =
        some (polyAt s.mem (Buf.addr s₀ (sB p r))) := by
      rcases h.out with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rw [e1] at h; exact absurd h (by decide)
    obtain ⟨x, hx, htx⟩ := Option.map_eq_some_iff.mp hb'
    refine ⟨h.kb.keep hp (N := 0) (by omega) sk fr' h', A, fun r' => if r' = r then x else S r', kA,
      fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [ifn (by omega)]; exact kS' r' hr'
      · rw [ifp rfl, htx, ← (m1 e1).2.1]
        exact ⟨⟨(m1 e1).2.2 (h.red e1), rfl⟩, Proof.MlDsa.KeyGen.rejBoundedPoly_range hx⟩
    · rw [ea]
      rcases hG with ⟨h1, b, hbA, hbS⟩ | ⟨h0, hn⟩
      · refine .inl ⟨aiff.mpr ⟨h1, e1⟩, bmax b b', fun e' he' =>
          Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hbA e' he'),
          fun r' hr' => ?_⟩
        dsimp only
        rcases (by omega : r' < r + 1 → r' < r ∨ r' = r) hr' with hr' | rfl
        · rw [ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejBounded
            (hbS r' hr')
        · rw [ifp rfl]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejBounded hx
      · rw [h0]
        exact .inr ⟨BitVec.zero_and, hn⟩

end

/-! ## The samplers, in sequence -/

theorem seqR_piece {Pre : State → Prop} {Pub : State → State → Prop} {f : Nat → Prog isa}
    {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → Piece Pre Pub (I k) (I (k + 1)) (f k)) →
      Piece Pre Pub (I a) (I (a + n)) (seqR f a n)
  | 0, a, _ => ⟨fun _ _ _ h => WP.block_nil_iff.mpr h, fun _ _ _ _ _ => RelCT.nil fun _ _ _ => trivial⟩
  | n + 1, a, h => by
    refine Piece.seq (h a (Nat.le_refl _) (by omega)) ?_
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact seqR_piece n (a + 1) fun k h₁ h₂ => h k (by omega) (by omega)

end VG.Proof.MlDsa.X86.KeyGen
