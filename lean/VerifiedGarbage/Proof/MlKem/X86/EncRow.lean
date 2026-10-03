import VerifiedGarbage.Proof.MlKem.X86.EncY

/-!
# ML-KEM on x86 (32-bit): `u` in K-PKE.Encrypt

Row `i` (`encRow L sc i`): each entry `Â[j, i]` is sampled from `ρ ‖ i ‖ j`,
masked by the value `vg_mlkem_sample_ntt` returned, which is ANDed into `eACC`
(`sample_piece`), and multiplied by `ŷ[j]` into `u[i]` (`entry0_piece`,
`entry_piece`); then `NTT⁻¹`, `e₁[i]` added, and `u[i]` compressed into the
ciphertext (`row_piece`).

`B k e` is what holds after `k` entries and `e` rows: `eACC` is 0 or 1; if 1,
the first `k` samples succeeded, and the first `e` rows of the ciphertext
are those of K-PKE.Encrypt for the matrix `aE` they sampled; if 0, one of the
`k²` samples failed within `minIterations` iterations. The seeds are
public: `ρ` is (`RhoPub`).
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {L : KemLay} {Y : Lay} {lk : State → List Byte}

section
variable (L : KemLay) (I : Inp) (s₀ : State)
/-- The seed of the `k`th entry sampled, `Â[k % k, k / k]`. -/
abbrev mSE (k : Nat) : List Byte := matSeed (ρE L I s₀) (k % L.p.k) (k / L.p.k)

/-- `Â[0, i] ×_T ŷ[0] + … + Â[j - 1, i] ×_T ŷ[j - 1]`. -/
noncomputable abbrev partU (i j : Nat) : Poly := KPke.dotK (fun j => aE L I s₀ j i) (yE I s₀) j
end

/-- Two runs with the same public data have the same `ρ`. -/
def RhoPub (L : KemLay) (Y : Lay) (lk : State → List Byte) (I : Inp) : Prop :=
  ∀ s₀ s₀', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → ρE L I s₀ = ρE L I s₀'

/-- `u[i]` in the ciphertext. -/
abbrev bCU (L : KemLay) (sc i : Nat) : Buf := ⟨sc, L.eC + 32 * L.p.du * i, 32 * L.p.du⟩

/-- See the module documentation. -/
structure B (L : KemLay) (Y : Lay) (I : Inp) (k e : Nat) (s₀ s : State) : Prop extends Base L Y I s₀ s where
  y : ∀ j < L.p.k, PolyIs s.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j)
  acc : accE L Y s₀ s = 0 ∨ accE L Y s₀ s = 1
  ok : accE L Y s₀ s = 1 → ∀ k' < k, ∃ a, Samp (mSE L I s₀ k') a
  fail : accE L Y s₀ s = 0 → ∃ k' < L.p.k * L.p.k, sampleNTT minIterations (mSE L I s₀ k') = none
  c : accE L Y s₀ s = 1 → ∀ i < e,
    bytesAt s.mem (Buf.addr s₀ (bCU L Y.sc i)) (32 * L.p.du) =
      compressEncode L.p.du (KPke.encU L.p (aE L I s₀) (rE I s₀) i)

/-- Whether `bs` is apart from the inputs and `ŷ`. -/
def safeS (L : KemLay) (Y : Lay) (bs : List Buf) : Bool :=
  inApart L Y bs && (List.range L.p.k).all fun j => Y.apart (bY Y.sc j) bs

/-- Whether `bs` is also apart from `eACC` and the rows of the ciphertext. -/
def safe (L : KemLay) (Y : Lay) (bs : List Buf) : Bool :=
  Y.apart (bACC L Y.sc) bs && safeS L Y bs && (List.range L.p.k).all fun i => Y.apart (bCU L Y.sc i) bs

/-- `sc_decide`, for facts that `safe` and `safeS` state. -/
macro "sc_decide'" : tactic => `(tactic| (simp only [safe, safeS]; sc_decide))

theorem keepS {I : Inp} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : safeS L Y bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (c : Ctx Y s₀ s') (h₁ : Base L Y I s₀ s)
    (h₂ : ∀ j < L.p.k, PolyIs s.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j)) :
    Base L Y I s₀ s' ∧ ∀ j < L.p.k, PolyIs s'.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j) := by
  simp only [safeS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  exact ⟨h₁.keep hp hM hs.1 fr c, fun j hj => keepPoly hp hM (hs.2 j hj) fr (h₂ j hj)⟩

theorem B.keep {I : Inp} {k e : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (hs : safe L Y bs = true) (he : e ≤ L.p.k) (fr : Frame (FR s₀ bs M) s.mem s'.mem)
    (h : B L Y I k e s₀ s) (c : Ctx Y s₀ s') : B L Y I k e s₀ s' := by
  simp only [safe, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hs
  have ea : accE L Y s₀ s' = accE L Y s₀ s := keepW hp hM h₁ fr
  obtain ⟨k₁, k₂⟩ := keepS hp hM h₂ fr c h.toBase h.y
  refine ⟨k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i hi => ?_⟩
  rw [keepBytes hp hM (h₃ i (by omega)) fr]
  exact h.c (ea ▸ e₁) i hi

/-- Before entry `(i, j)`: and `u[i]` so far, if `0 < j`. -/
structure R (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop
    extends B L Y I (L.p.k * i + j) i s₀ s where
  u : 0 < j → Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧
    (accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = partU L I s₀ i j)

theorem R.keep {I : Inp} {i j : Nat} (hi : i < L.p.k) {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf}
    {M : Nat} (hM : M + 16 ≤ Y.stk) (hs : safe L Y bs = true) (hU : Y.apart (bU L Y.sc) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : R L Y I i j s₀ s) (c : Ctx Y s₀ s') : R L Y I i j s₀ s' := by
  have k := h.toB.keep hp hM hs (by omega) fr c
  have ea : accE L Y s₀ s' = accE L Y s₀ s :=
    keepW hp hM (by simp only [safe, Bool.and_eq_true] at hs; exact hs.1.1) fr
  refine ⟨k, fun hj => ⟨keepRed hp hM hU fr (h.u hj).1, fun e₁ => ?_⟩⟩
  rw [polyAt_congr (Top.keep hp hM hU fr)]
  exact (h.u hj).2 (ea ▸ e₁)

/-- The facts of the layout that an entry uses. -/
class EntOK (L : KemLay) : Prop where
  seed : ∀ {Y : Lay}, SOK L Y → Y.ok ⟨Y.sc, L.eEK + 384 * L.p.k, 32⟩ = true ∧ Y.ok (bEK L Y.sc) = true ∧
    Y.ok ⟨Y.sc, L.eEK + L.p.ekLen, 2⟩ = true ∧ Y.ok ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩ = true ∧
    Y.ok ⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩ = true ∧ Y.okW ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩ = true ∧
    Y.okW ⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩ = true
  ent : ∀ {Y : Lay}, SOK L Y →
    safe L Y [⟨Y.sc, L.eEK + L.p.ekLen, 1⟩] = true ∧ safe L Y [⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩] = true ∧
    Y.apart (bU L Y.sc) [⟨Y.sc, L.eEK + L.p.ekLen, 1⟩] = true ∧
    Y.apart (bU L Y.sc) [⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩] = true ∧
    Y.apart ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩ [⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩] = true ∧
    safe L Y [bA L Y.sc, bSS L Y.sc] = true ∧ Y.apart (bU L Y.sc) [bA L Y.sc, bSS L Y.sc] = true ∧
    safeS L Y [bACC L Y.sc, bA L Y.sc] = true ∧
    (∀ i < L.p.k, Y.apart (bCU L Y.sc i) [bACC L Y.sc, bA L Y.sc] = true) ∧
    Y.apart (bU L Y.sc) [bACC L Y.sc, bA L Y.sc] = true ∧
    (Y.ok (bSeed L Y.sc) && Y.okW (bA L Y.sc) && Y.okW (bSS L Y.sc) && Y.sep (bSeed L Y.sc) (bA L Y.sc) &&
      Y.sep (bSeed L Y.sc) (bSS L Y.sc) && Y.sep (bA L Y.sc) (bSS L Y.sc)) = true ∧
    (Y.okW (bACC L Y.sc) && Y.okW (bA L Y.sc) && Y.sep (bACC L Y.sc) (bA L Y.sc)) = true
  mul : ∀ {Y : Lay}, SOK L Y →
    safe L Y [bU L Y.sc, bNS L Y.sc] = true ∧ safe L Y [bP L Y.sc, bNS L Y.sc] = true ∧
    safe L Y [bU L Y.sc] = true ∧ Y.apart (bU L Y.sc) [bP L Y.sc, bNS L Y.sc] = true ∧
    Y.apart (bA L Y.sc) [bP L Y.sc, bNS L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bU L Y.sc, bNS L Y.sc] = true ∧
    Y.apart (bACC L Y.sc) [bP L Y.sc, bNS L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bU L Y.sc] = true ∧
    (Y.okW (bU L Y.sc) && Y.ok (bA L Y.sc) && Y.ok (bY Y.sc 0) && Y.okW (bNS L Y.sc) &&
      Y.sep (bU L Y.sc) (bA L Y.sc) && Y.sep (bU L Y.sc) (bY Y.sc 0) && Y.sep (bU L Y.sc) (bNS L Y.sc) &&
      Y.sep (bA L Y.sc) (bNS L Y.sc) && Y.sep (bY Y.sc 0) (bNS L Y.sc)) = true ∧
    (∀ j < L.p.k, (Y.okW (bP L Y.sc) && Y.ok (bA L Y.sc) && Y.ok (bY Y.sc j) && Y.okW (bNS L Y.sc) &&
      Y.sep (bP L Y.sc) (bA L Y.sc) && Y.sep (bP L Y.sc) (bY Y.sc j) && Y.sep (bP L Y.sc) (bNS L Y.sc) &&
      Y.sep (bA L Y.sc) (bNS L Y.sc) && Y.sep (bY Y.sc j) (bNS L Y.sc)) = true) ∧
    (Y.okW (bU L Y.sc) && Y.ok (bP L Y.sc) && Y.sep (bU L Y.sc) (bP L Y.sc)) = true

theorem mSE_eq (I : Inp) (s₀ : State) {i j : Nat} (hj : j < L.p.k) :
    mSE L I s₀ (L.p.k * i + j) = matSeed (ρE L I s₀) j i := by
  simp only [mSE]
  rw [idx_mod hj, idx_div hj]

variable [EntOK L]

/-! ## The seed -/

/-- `ρ`, in `ek`. -/
theorem rho_eq (hS : SOK L Y) {I : Inp} {s₀ s : State} (hp : TPre Y s₀) (h : Base L Y I s₀ s) :
    bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, L.eEK + 384 * L.p.k, 32⟩) 32 = ρE L I s₀ := by
  obtain ⟨o₁, o₂, -⟩ := EntOK.seed hS
  rw [show ρE L I s₀ = ((I.ek s₀).drop (384 * L.p.k)).take 32 from rfl, ← h.ek,
    bytesAt_slice _ _ (show 384 * L.p.k + 32 ≤ L.p.ekLen from Nat.le_refl _)]
  rw [Buf.addr_eq hp (b := ⟨Y.sc, L.eEK + 384 * L.p.k, 32⟩) o₁, Buf.addr_eq hp (b := bEK L Y.sc) o₂,
    BitVec.add_assoc, ← BitVec.ofNat_add]

theorem seed_split (hS : SOK L Y) {s₀ : State} (hp : TPre Y s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (bSeed L Y.sc)) 34 = bytesAt m (Buf.addr s₀ ⟨Y.sc, L.eEK + 384 * L.p.k, 32⟩) 32 ++
      (bytesAt m (Buf.addr s₀ ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩) 1 ++
        bytesAt m (Buf.addr s₀ ⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩) 1) := by
  obtain ⟨o₁, -, o₃, o₄, o₅, -⟩ := EntOK.seed hS
  rw [bytes_split hp m (o' := L.eEK + L.p.ekLen) (l₁ := 32) (l₂ := 2) (by rw [Nat.add_assoc]; rfl) rfl o₁ o₃,
    bytes_split hp m (a := Y.sc) (o := L.eEK + L.p.ekLen) (o' := L.eEK + L.p.ekLen + 1) (l₁ := 1) (l₂ := 1) rfl
      rfl o₄ o₅]

/-! ## An entry -/

/-- After `i` is stored. -/
structure S1 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends R L Y I i j s₀ s where
  bi : bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩) 1 = [BitVec.ofNat 8 i]

/-- After `ρ ‖ i ‖ j` is stored. -/
structure S2 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends R L Y I i j s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (bSeed L Y.sc)) 34 = matSeed (ρE L I s₀) j i

/-- After `Â[j, i]` is sampled, `r` returned. -/
structure S3 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends R L Y I i j s₀ s where
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (bA L Y.sc))
  out : Outcome (fun iters => sampleNTT iters (matSeed (ρE L I s₀) j i)) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (bA L Y.sc)))

/-- After it is masked, and `eACC` updated. -/
structure S4 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop
    extends B L Y I (L.p.k * i + j + 1) i s₀ s where
  u : 0 < j → Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧
    (accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = partU L I s₀ i j)
  red : Reduced s.mem (Buf.addr s₀ (bA L Y.sc))
  a : accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bA L Y.sc)) = aE L I s₀ j i

/-- `ρ ‖ i ‖ j`, `Â[j, i]` sampled and masked, then `c`. -/
theorem sample_piece (hS : SOK L Y) {I : Inp} (hρ : RhoPub L Y lk I) (i j : Nat) (hi : i < L.p.k)
    (hj : j < L.p.k) {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre Y) (TPub Y lk) (S4 L Y I i j) Q c) :
    Piece (TPre Y) (TPub Y lk) (R L Y I i j) Q
      (.seq (.block (st8 (L.eEK + L.p.ekLen) i)) <| .seq (.block (st8 (L.eEK + L.p.ekLen + 1) j)) <|
        .seq (sampleC Y.sc (bSeed L Y.sc) (bA L Y.sc) (bSS L Y.sc)) (.seq (maskA L.eACC L.eA) c)) := by
  obtain ⟨n₁, n₂, n₃, n₄, n₅, p₁, p₂, q₁, q₂, q₃, hs, hm⟩ := EntOK.ent hS
  obtain ⟨-, -, -, -, -, w₁, w₂⟩ := EntOK.seed hS
  have k88 : 0 + 16 ≤ Y.stk := hS.le
  refine Piece.seq (B := S1 L Y I i j) (st8_piece (Y := Y) (L.eEK + L.p.ekLen) i w₁ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hi hp k88 n₁ n₃ (m' ▸ frW8) h', by rw [m']; exact st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := S2 L Y I i j) (st8_piece (Y := Y) (L.eEK + L.p.ekLen + 1) j w₂ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ?_) ?_
  · have k := h.keep hi hp k88 n₂ n₄ (m' ▸ frW8) h'
    refine ⟨k, ?_⟩
    rw [seed_split hS hp, rho_eq hS hp k.toBase, keepBytes hp k88 n₅ (m' ▸ frW8), h.bi, m', st8_byte]
    rfl
  refine Piece.seq (B := S3 L Y I i j) (sampleC_piece (Y := Y) Y.sc (L.eEK + 384 * L.p.k) Y.sc L.eA Y.sc L.eSS
    hs hS.le (by sc_taint) (fun _ _ _ h => h.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => ?_)
    fun s₀ s s' hp h h' fr red out => ⟨h.keep hi hp hS.le p₁ p₂ fr h', red, ?_⟩) ?_
  · rw [h.seed, h'.seed, hρ s₀ s₀' hp hp' hq]
  · rw [h.seed] at out; exact out
  refine Piece.seq (maskA_piece (Y := Y) L.eACC L.eA hm (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_) hc
  have fr' := fr2 fr
  have hr := outcome_01 h.out
  have ea : accE L Y s₀ s' = accE L Y s₀ s &&& s.gpr .eax := ha
  obtain ⟨s₁, s₂, s₃⟩ := acc_step h.acc hr
  rw [← ea] at s₁ s₂ s₃
  obtain ⟨k₁, k₂⟩ := keepS hp k88 q₁ fr' h' h.toBase h.y
  obtain ⟨mr, ma⟩ := mask_poly hr hc h.red
  refine ⟨⟨k₁, k₂, s₁, fun e₁ k' hk' => ?_, fun e₁ => ?_, fun e₁ i' hi' => ?_⟩,
    fun hj => ⟨keepRed hp k88 q₃ fr' (h.u hj).1, fun e₁ => ?_⟩, mr, fun e₁ => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · exact h.ok (s₂ e₁).1 k' hk'
    · rw [mSE_eq I s₀ hj]
      rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
      · exact ⟨_, it, e⟩
      · exact absurd ((s₂ e₁).2) (by rw [e]; decide)
  · rcases s₃ e₁ with e₂ | e₂
    · exact h.fail e₂
    · refine ⟨L.p.k * i + j, idx_lt hi hj, ?_⟩
      rw [mSE_eq I s₀ hj]
      rcases h.out with ⟨e, _⟩ | ⟨_, e⟩
      · exact absurd e (by rw [e₂]; decide)
      · exact e
  · rw [keepBytes hp k88 (q₂ i' (by omega)) fr']
    exact h.c (s₂ e₁).1 i' hi'
  · rw [polyAt_congr (Top.keep hp k88 q₃ fr')]
    exact (h.u hj).2 (s₂ e₁).1
  · refine (ma (s₂ e₁).2).trans ?_
    rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
    · exact (sv_eq ⟨it, e⟩).symm
    · exact absurd ((s₂ e₁).2) (by rw [e]; decide)

/-- After `Â[j, i] ×_T ŷ[j]` is computed, for `0 < j`. -/
structure S5 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends S4 L Y I i j s₀ s where
  p : Reduced s.mem (Buf.addr s₀ (bP L Y.sc)) ∧
    (accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bP L Y.sc)) = multiplyNTTs (aE L I s₀ j i) (yE I s₀ j))

/-- Entry `(i, 0)`: `u[i] ← Â[0, i] ×_T ŷ[0]`. -/
theorem entry0_piece (hS : SOK L Y) {I : Inp} (hρ : RhoPub L Y lk I) (i : Nat) (hi : i < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (R L Y I i 0) (R L Y I i 1) (encEntry L Y.sc i 0) := by
  obtain ⟨m₁, -, -, -, -, a₁, -, -, o₁, -, -⟩ := EntOK.mul hS
  have hk : 0 < L.p.k := by omega
  refine sample_piece hS hρ i 0 hi hk (mulC_piece (Y := Y) Y.sc L.eU Y.sc L.eA Y.sc 0 Y.sc L.eNS
    o₁ hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.y 0 hk).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  have k := h.toB.keep hp hS.le m₁ (by omega) fr h'
  have ea : accE L Y s₀ s' = accE L Y s₀ s := keepW hp hS.le a₁ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, h.a (ea ▸ e₁), (h.y 0 hk).2]
  rfl

/-- Entry `(i, j + 1)`: `u[i] ← u[i] + Â[j + 1, i] ×_T ŷ[j + 1]`. -/
theorem entry_piece (hS : SOK L Y) {I : Inp} (hρ : RhoPub L Y lk I) (i j : Nat) (hi : i < L.p.k)
    (hj : j + 1 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (R L Y I i (j + 1)) (R L Y I i (j + 2)) (encEntry L Y.sc i (j + 1)) := by
  obtain ⟨-, m₂, m₃, m₄, m₅, -, a₂, a₃, -, o₂, o₃⟩ := EntOK.mul hS
  refine sample_piece hS hρ i (j + 1) hi hj (.seq (B := S5 L Y I i (j + 1))
    (mulC_piece (Y := Y) Y.sc L.eP Y.sc L.eA Y.sc (1024 * (j + 1)) Y.sc L.eNS (o₂ (j + 1) hj) hS.le
      (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.y (j + 1) (by omega)).1⟩)
      fun s₀ s s' hp h h' fr post => ?_) ?_)
  · have k := h.toB.keep hp hS.le m₂ (by omega) fr h'
    have ea : accE L Y s₀ s' = accE L Y s₀ s := keepW hp hS.le a₂ fr
    refine ⟨⟨k, fun hj' => ⟨keepRed hp hS.le m₄ fr (h.u hj').1, fun e₁ => ?_⟩,
      keepRed hp hS.le m₅ fr h.red, fun e₁ => ?_⟩, post.1, fun e₁ => ?_⟩
    · rw [polyAt_congr (Top.keep hp hS.le m₄ fr)]; exact (h.u hj').2 (ea ▸ e₁)
    · rw [polyAt_congr (Top.keep hp hS.le m₅ fr)]; exact h.a (ea ▸ e₁)
    · rw [post.2, h.a (ea ▸ e₁), (h.y (j + 1) (by omega)).2]
  refine accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eP o₃ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.u (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.toB.keep hp hS.le m₃ (by omega) fr h'
  have ea : accE L Y s₀ s' = accE L Y s₀ s := keepW hp hS.le a₃ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, (h.u (Nat.succ_pos _)).2 (ea ▸ e₁), h.p.2 (ea ▸ e₁)]
  rfl

/-- The `k` entries of row `i`, then `c`. -/
theorem entries_piece (hS : SOK L Y) {I : Inp} (hρ : RhoPub L Y lk I) (i : Nat) (hi : i < L.p.k)
    {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (R L Y I i L.p.k) Q c) :
    Piece (TPre Y) (TPub Y lk) (R L Y I i 0) Q (seqs ((List.range L.p.k).map (encEntry L Y.sc i)) c) :=
  Piece.seqs0 (P := R L Y I i) L.p.k (fun j hj => match j, hj with
    | 0, _ => entry0_piece hS hρ i hi
    | j + 1, hj => entry_piece hS hρ i j hi hj) hc

end VG.Proof.MlKem.X86.Enc
