import VerifiedGarbage.Proof.MlDsa.X86.Verify.Hint
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp

/-!
# ML-DSA verification on x86 (32-bit): the samplers

Once the hint is well formed and the norms of `z` within the bound (`VB`), `ρ`
is copied to the seed, and each entry `e = 8r + s` of `Â` sampled from `ρ ‖ s
‖ r` (`aOne_piece`), the sampler's result ANDed into the result and the
polynomial masked with it, as in key generation; then `c` from `c̃`
(`samples_piece`). The result is 1 if the samplers' outputs are those of the
standard for some bounds, and 0 if verification is not true within the least
bounds (`GA`, `GC`).
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly sampleInBall PolyIs Reduced polyAt toRq)
open VG.Proof.MlDsa.Verify (vZ vHint vRho vCt aSeed)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params) (s₀ : State)

/-- After `z`: the hint and `z` stored, and the norms of `z` within the bound. -/
structure VB (s : State) : Prop where
  ctx : Ctx (YV p) s₀ s
  hint : HOk p s₀ s
  z : ∀ j < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pZ j)) (toRq (vZ p (vSig p s₀) j))
  norms : NormsOk p s₀ p.ℓ

/-- Verification is not true within the least bounds. -/
abbrev VFail : Prop := Spec.MlDsa.verifyMu p minBounds (vPk p s₀) (vMu s₀) (vSig p s₀) ≠ some true

/-- The entries `(r, s)` of `Â` before `e = 8r + s`. -/
abbrev Before (e r s : Nat) : Prop := s < p.ℓ ∧ 8 * r + s < e

/-- The result after the entries of `Â` before `e`, those of `A`. -/
def GA (e : Nat) (A : Nat → Nat → Poly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, ∀ r s, Before p e r s → rejNTTPoly b.rejNTT (aSeed (vPk p s₀) r s) = some (A r s)) ∨
    (v = 0 ∧ VFail p s₀)

/-- After the entries of `Â` before `e`. -/
structure SA (e : Nat) (s : State) : Prop where
  vb : VB p s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ (sb oSB 32)) 32 = vRho (vPk p s₀)
  ex : ∃ A : Nat → Nat → Poly, (∀ r s', Before p e r s' → PolyIs s.mem (Buf.addr s₀ (pA r s')) (A r s')) ∧
    GA p s₀ e A (accV s₀ s)

/-- The result after `Â` and `c`, those of `A` and `C`. -/
def GC (A : Nat → Nat → Poly) (C : Poly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ (b : Bounds) (c : IPoly), (∀ r < p.k, ∀ s < p.ℓ,
      rejNTTPoly b.rejNTT (aSeed (vPk p s₀) r s) = some (A r s)) ∧
      sampleInBall p.τ b.ball (vCt p (vSig p s₀)) = some c ∧ toRq c = C) ∨
    (v = 0 ∧ VFail p s₀)

/-- After `Â` and `c`. -/
structure SC (s : State) : Prop where
  vb : VB p s₀ s
  ex : ∃ (A : Nat → Nat → Poly) (C : Poly), (∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pA r s')) (A r s')) ∧
    PolyIs s.mem (Buf.addr s₀ pC) C ∧ GC p s₀ A C (accV s₀ s)

end

/-! ## Keeping the facts -/

theorem VB.keep {p : Params} {s₀ s s' : State} (h : VB p s₀ s) (hp : TPre (YV p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (sh : (YV p).apart (hB p.k) bs = true) (sz : ∀ j < p.ℓ, (YV p).apart (pZ j) bs = true)
    (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : Ctx (YV p) s₀ s') : VB p s₀ s' :=
  ⟨h', h.hint.keep hp hN sh fr, fun j hj => keepPolyD hp (stkV hN) (sz j hj) fr (h.z j hj), h.norms⟩

theorem SA.keep {p : Params} {e : Nat} {s₀ s s' : State} (h : SA p s₀ e s) (hp : TPre (YV p) s₀) {bs : List Buf}
    {N : Nat} (hN : N + 16 ≤ 96) (sh : (YV p).apart (hB p.k) bs = true)
    (sz : ∀ j < p.ℓ, (YV p).apart (pZ j) bs = true) (sr : (YV p).apart (sb oSB 32) bs = true)
    (sa : (YV p).apart (sb oACC 4) bs = true) (sA : ∀ r s, Before p e r s → (YV p).apart (pA r s) bs = true)
    (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : Ctx (YV p) s₀ s') : SA p s₀ e s' := by
  obtain ⟨A, hA, hG⟩ := h.ex
  refine ⟨h.vb.keep hp hN sh sz fr h', by rw [keepBytes hp (stkV hN) sr fr]; exact h.rho,
    A, fun r s hb => keepPolyD hp (stkV hN) (sA r s hb) fr (hA r s hb), ?_⟩
  rw [acc_keepV hp hN sa fr]; exact hG

theorem SA.congr {p : Params} {e e' : Nat} {s₀ s : State} (h : SA p s₀ e s)
    (he : ∀ r s, s < p.ℓ → (8 * r + s < e ↔ 8 * r + s < e')) : SA p s₀ e' s := by
  obtain ⟨A, hA, hG⟩ := h.ex
  refine ⟨h.vb, h.rho, A, fun r s hb => hA r s ⟨hb.1, (he r s hb.1).mpr hb.2⟩, ?_⟩
  rcases hG with ⟨h1, b, hb⟩ | h0
  · exact .inl ⟨h1, b, fun r s hb' => hb r s ⟨hb'.1, (he r s hb'.1).mpr hb'.2⟩⟩
  · exact .inr h0

/-! ## An entry of `Â` -/

theorem aSeed_eq (pk : List Byte) (r s : Nat) :
    aSeed pk r s = vRho pk ++ ([BitVec.ofNat 8 s] ++ [BitVec.ofNat 8 r]) := by
  simp only [aSeed, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]

theorem pA_eq (e : Nat) : pA (e / 8) (e % 8) = pB (20 + e) := by
  show pB (20 + 8 * (e / 8) + e % 8) = pB (20 + e)
  rw [show 20 + 8 * (e / 8) + e % 8 = 20 + e by omega]

section
variable (p : Params)

/-- After the first byte of the seed of entry `e`. -/
abbrev SA1 (e : Nat) (s₀ s : State) : Prop :=
  SA p s₀ e s ∧ bytesAt s.mem (Buf.addr s₀ (sb (oSB + 32) 1)) 1 = [BitVec.ofNat 8 (e % 8)]

/-- With the seed of entry `e`. -/
abbrev SA2 (e : Nat) (s₀ s : State) : Prop :=
  SA p s₀ e s ∧ bytesAt s.mem (Buf.addr s₀ (sb oSB 34)) 34 = aSeed (vPk p s₀) (e / 8) (e % 8)

/-- After `RejNTTPoly` for entry `e`. -/
structure SA3 (e : Nat) (s₀ s : State) : Prop where
  vb : VB p s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ (sb oSB 32)) 32 = vRho (vPk p s₀)
  ex : ∃ A : Nat → Nat → Poly, (∀ r s', Before p e r s' → PolyIs s.mem (Buf.addr s₀ (pA r s')) (A r s')) ∧
    GA p s₀ e A (accV s₀ s)
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (pB (20 + e)))
  out : Spec.MlDsa.Outcome (fun b => rejNTTPoly b.rejNTT (aSeed (vPk p s₀) (e / 8) (e % 8))) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (pB (20 + e))))

end

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p) {e : Nat} (he : e < 8 * p.k)
  (hel : e % 8 < p.ℓ)
include hF he

theorem sa_st1 : VP p (SA p · e) (SA1 p e) (.block (st8 (oSB + 32) (e % 8))) :=
  st8_piece (Y := YV p) (oSB + 32) (e % 8) (by lv hF) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => h.vb.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) (by lv hF) (by lv hF)
        (fun r s hb => by have := hb.1; have := hb.2; lv hF) (m' ▸ frW8 (Y := YV p)) h',
        by rw [m']; exact st8_bytes _ _ _ _ _⟩

theorem sa_st2 : VP p (SA1 p e) (SA2 p e) (.block (st8 (oSB + 33) (e / 8))) :=
  st8_piece (Y := YV p) (oSB + 33) (e / 8) (by lv hF) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => h.1.vb.ctx) fun s₀ s s' hp h h' m' => by
      have fr : Frame (FR s₀ [sb (oSB + 33) 1] 0) s.mem s'.mem := m' ▸ frW8 (Y := YV p)
      refine ⟨h.1.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) (by lv hF) (by lv hF)
        (fun r s hb => by have := hb.1; have := hb.2; lv hF) fr h', ?_⟩
      have k32 := keepBytes hp (N := 0) (stkV (by omega)) (b := sb oSB 32) (by lv hF) fr
      have k1 := keepBytes hp (N := 0) (stkV (by omega)) (b := sb (oSB + 32) 1) (by lv hF) fr
      rw [show (34 : Nat) = 32 + (1 + 1) from rfl, bytes_cat hp _ (l₁ := 32) (by lv hF) (by lv hF),
        bytes_cat hp _ (l₁ := 1) (l₂ := 1) (by lv hF) (by lv hF), k32, k1, h.1.rho, h.2, aSeed_eq, m']
      exact congrArg (fun x => vRho (vPk p s₀) ++ ([BitVec.ofNat 8 (e % 8)] ++ x)) (st8_bytes _ _ _ _ _)

include hP in
theorem sa_rej : VP p (SA2 p e) (SA3 p e)
    (Impl.MlDsa.X86.KeyGen.callPR vS "vg_mldsa_rej_ntt_poly" P.rejNtt
      [.buf (sb oSB 34), .buf (pB (20 + e)), .buf (ssB 2048)]) :=
  rejNtt_piece (Y := YV p) hP.rejNtt vS oSB vS (oP (20 + e)) vS oSS (by lv hF) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.vb.ctx)
    (fun s₀ s₀' s s' _ _ hq h h' => by rw [h.2, h'.2, (inputs_pub hq).1])
    fun s₀ s s' hp h h' fr red out => by
      obtain ⟨A, hA, hG⟩ := h.1.ex
      refine ⟨h.1.vb.keep hp (N := 80) (by omega) (by lv hF) (fun j hj => by lv hF) fr h',
        by rw [keepBytes hp (N := 80) (stkV (by omega)) (by lv hF) fr]; exact h.1.rho,
        ⟨A, fun r s hb => keepPolyD hp (stkV (by omega)) (by have := hb.1; have := hb.2; lv hF) fr (hA r s hb), ?_⟩,
        red, by rw [← h.2]; exact out⟩
      rw [acc_keepV hp (N := 80) (by omega) (by lv hF) fr]; exact hG

include hel in
theorem sa_mask : VP p (SA3 p e) (SA p · (e + 1)) (maskA oACC (oP (20 + e))) := by
  have hl := hF.l
  refine maskA_piece (Y := YV p) oACC (oP (20 + e)) (by lv hF) (maskA_tt _) (fun _ _ _ h => h.vb.ctx)
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
  have fr' : Frame (FR s₀ [sb oACC 4, pB (20 + e)] 0) s.mem s'.mem := fr2 fr
  have ea : accV s₀ s' = accV s₀ s &&& s.gpr .eax := ha
  have hr : e / 8 < p.k := by omega
  have hq : 8 * (e / 8) + e % 8 = e := Nat.div_add_mod e 8
  refine ⟨h.vb.keep hp (N := 0) (by omega) (by lv hF) (fun j hj => by lv hF) fr' h',
    by rw [keepBytes hp (N := 0) (stkV (by omega)) (by lv hF) fr']; exact h.rho,
    fun r s => if r = e / 8 ∧ s = e % 8 then polyAt s'.mem (Buf.addr s₀ (pB (20 + e))) else A r s,
    fun r s hb => ?_, ?_⟩
  · dsimp only
    by_cases hrs : r = e / 8 ∧ s = e % 8
    · obtain ⟨rfl, rfl⟩ := hrs
      rw [ifp ⟨rfl, rfl⟩, pA_eq e]
      refine ⟨?_, rfl⟩
      rcases r01 with e0 | e1
      · exact (m0 e0).1
      · exact (m1 e1).2.2 (h.red e1)
    · rw [ifn hrs]
      have hb' : Before p e r s := ⟨hb.1, by
        have := hb.2
        rcases (by omega : 8 * r + s < e ∨ 8 * r + s = e) with h | h
        · exact h
        · exact absurd ⟨by omega, by omega⟩ hrs⟩
      exact keepPolyD hp (stkV (by omega)) (by have := hb'.1; have := hb'.2; lv hF) fr' (hA r s hb')
  · rw [ea]
    rcases hG with ⟨h1, b, hb⟩ | ⟨h0, hn⟩
    · rcases h.out with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨aiff.mpr ⟨h1, ho⟩, Proof.MlDsa.Verify.bmax b b', fun r s hb₁ => ?_⟩
        dsimp only
        by_cases hrs : r = e / 8 ∧ s = e % 8
        · obtain ⟨rfl, rfl⟩ := hrs
          rw [ifp ⟨rfl, rfl⟩, (m1 ho).2.1]
          exact Proof.MlDsa.Verify.rejNTTPoly_mono (Proof.MlDsa.Verify.bmax_right b b').rejNTT hb'
        · rw [ifn hrs]
          refine Proof.MlDsa.Verify.rejNTTPoly_mono (Proof.MlDsa.Verify.bmax_left b b').rejNTT (hb r s ⟨hb₁.1, ?_⟩)
          have := hb₁.2
          rcases (by omega : 8 * r + s < e ∨ 8 * r + s = e) with h | h
          · exact h
          · exact absurd ⟨by omega, by omega⟩ hrs
      · rw [ho, h1]
        obtain ⟨hh, ehh, -⟩ := h.vb.hint
        exact .inr ⟨by decide, by
          show Spec.MlDsa.verifyMu p minBounds (vPk p s₀) (vMu s₀) (vSig p s₀) ≠ some true
          rw [Proof.MlDsa.Verify.verifyMu_rej_none minBounds _ _ ehh hr hel hn]; exact fun h => nomatch h⟩
    · rw [h0]
      exact .inr ⟨BitVec.zero_and, hn⟩

include hP hel in
theorem aOne_piece : VP p (SA p · e) (SA p · (e + 1)) (aOne P e) := by
  unfold aOne
  exact (sa_st1 hF he).seq ((sa_st2 hF he).seq ((sa_rej hP hF he).seq (sa_mask hF he hel)))

end

/-! ## `Â` and `c` -/

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

theorem aRow_piece {r : Nat} (hr : r < p.k) : VP p (SA p · (8 * r)) (SA p · (8 * (r + 1))) (aRow P p r) := by
  have hl := hF.l
  unfold aRow
  refine (seqR_piece (I := fun e => (SA p · e)) p.ℓ (8 * r) fun e h₁ h₂ =>
    aOne_piece hP hF (by omega) (by omega)).mono (fun _ _ _ h => h) fun _ _ _ h => h.congr fun r' s hs => ?_
  omega

end

end VG.Proof.MlDsa.X86.Verify
