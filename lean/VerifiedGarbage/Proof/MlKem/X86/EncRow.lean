import VerifiedGarbage.Proof.MlKem.X86.EncY

/-!
# ML-KEM-768 on x86 (32-bit): `u` in K-PKE.Encrypt

Untrusted: everything here is checked by Lean. Row `i` (`encRow i`): each
entry `Â[j, i]` is sampled from `ρ ‖ i ‖ j`, masked by the value
`vg_mlkem_sample_ntt` returned, which is ANDed into `eACC` (`sample_piece`),
and multiplied by `ŷ[j]` into `u[i]` (`entry0_piece`, `entry_piece`); then
`NTT⁻¹`, `e₁[i]` added, and `u[i]` compressed into the ciphertext
(`row_piece`).

`B k e` is what holds after `k` entries and `e` rows: `eACC` is 0 or 1; if 1,
the first `k` samples succeeded, and the first `e` rows of the ciphertext
are those of K-PKE.Encrypt for the matrix `aE` they sampled; if 0, one of the
nine samples failed within `minIterations` iterations. The seeds are
public: `ρ` is (`RhoPub`).
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {Y : Lay} {lk : State → List Byte}

section
variable (I : Inp) (s₀ : State)
/-- The seed of the `k`th entry sampled, `Â[k % 3, k / 3]`. -/
abbrev mSE (k : Nat) : List Byte := matSeed (ρE I s₀) (k % 3) (k / 3)

/-- `Â[0, i] ×_T ŷ[0] + … + Â[j - 1, i] ×_T ŷ[j - 1]`, for `0 < j`. -/
noncomputable def partU (i : Nat) : Nat → Poly
  | 0 => zero
  | 1 => multiplyNTTs (aE I s₀ 0 i) (yE I s₀ 0)
  | j + 1 => add (partU i j) (multiplyNTTs (aE I s₀ j i) (yE I s₀ j))
end

/-- Two runs with the same public data have the same `ρ`. -/
def RhoPub (Y : Lay) (lk : State → List Byte) (I : Inp) : Prop :=
  ∀ s₀ s₀', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → ρE I s₀ = ρE I s₀'

/-- `u[i]` in the ciphertext. -/
abbrev bCU (sc i : Nat) : Buf := ⟨sc, eC + 320 * i, 320⟩

/-- See the module documentation. -/
structure B (Y : Lay) (I : Inp) (k e : Nat) (s₀ s : State) : Prop extends Base Y I s₀ s where
  y : ∀ j < 3, PolyIs s.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j)
  acc : accE Y s₀ s = 0 ∨ accE Y s₀ s = 1
  ok : accE Y s₀ s = 1 → ∀ k' < k, ∃ a, Samp (mSE I s₀ k') a
  fail : accE Y s₀ s = 0 → ∃ k' < 9, sampleNTT minIterations (mSE I s₀ k') = none
  c : accE Y s₀ s = 1 → ∀ i < e,
    bytesAt s.mem (Buf.addr s₀ (bCU Y.sc i)) 320 = compressEncode 10 (encU (aE I s₀) (rE I s₀) i)

/-- Whether `bs` is apart from the inputs and `ŷ`. -/
def safeS (Y : Lay) (bs : List Buf) : Bool := inApart Y bs && (List.range 3).all fun j => Y.apart (bY Y.sc j) bs

/-- Whether `bs` is also apart from `eACC` and the rows of the ciphertext. -/
def safe (Y : Lay) (bs : List Buf) : Bool :=
  Y.apart (bACC Y.sc) bs && safeS Y bs && (List.range 3).all fun i => Y.apart (bCU Y.sc i) bs

/-- `sc_decide`, for facts that `safe` and `safeS` state. -/
macro "sc_decide'" : tactic => `(tactic| (simp only [safe, safeS]; sc_decide))

theorem keepS {I : Inp} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : safeS Y bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (c : Ctx Y s₀ s') (h₁ : Base Y I s₀ s)
    (h₂ : ∀ j < 3, PolyIs s.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j)) :
    Base Y I s₀ s' ∧ ∀ j < 3, PolyIs s'.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j) := by
  simp only [safeS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  exact ⟨h₁.keep hp hM hs.1 fr c, fun j hj => keepPoly hp hM (hs.2 j hj) fr (h₂ j hj)⟩

theorem B.keep {I : Inp} {k e : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (hs : safe Y bs = true) (he : e ≤ 3) (fr : Frame (FR s₀ bs M) s.mem s'.mem)
    (h : B Y I k e s₀ s) (c : Ctx Y s₀ s') : B Y I k e s₀ s' := by
  simp only [safe, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hs
  have ea : accE Y s₀ s' = accE Y s₀ s := keepW hp hM h₁ fr
  obtain ⟨k₁, k₂⟩ := keepS hp hM h₂ fr c h.toBase h.y
  refine ⟨k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i hi => ?_⟩
  rw [keepBytes hp hM (h₃ i (by omega)) fr]
  exact h.c (ea ▸ e₁) i hi

/-- Before entry `(i, j)`: and `u[i]` so far, if `0 < j`. -/
structure R (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends B Y I (3 * i + j) i s₀ s where
  u : 0 < j → Reduced s.mem (Buf.addr s₀ (bU Y.sc)) ∧
    (accE Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU Y.sc)) = partU I s₀ i j)

theorem R.keep {I : Inp} {i j : Nat} (hi : i < 3) {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (hs : safe Y bs = true) (hU : Y.apart (bU Y.sc) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : R Y I i j s₀ s) (c : Ctx Y s₀ s') : R Y I i j s₀ s' := by
  have k := h.toB.keep hp hM hs (by omega) fr c
  have ea : accE Y s₀ s' = accE Y s₀ s := keepW hp hM (by simp only [safe, Bool.and_eq_true] at hs; exact hs.1.1) fr
  refine ⟨k, fun hj => ⟨keepRed hp hM hU fr (h.u hj).1, fun e₁ => ?_⟩⟩
  rw [polyAt_congr (Top.keep hp hM hU fr)]
  exact (h.u hj).2 (ea ▸ e₁)

/-! ## The seed -/

/-- `ρ`, in `ek`. -/
theorem rho_eq (hS : SOK Y) {I : Inp} {s₀ s : State} (hp : TPre Y s₀) (h : Base Y I s₀ s) :
    bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, eEK + 1152, 32⟩) 32 = ρE I s₀ := by
  rw [show ρE I s₀ = ((I.ek s₀).drop 1152).take 32 from rfl, ← h.ek,
    bytesAt_slice _ _ (show 1152 + 32 ≤ 1184 by decide)]
  rw [Buf.addr_eq hp (b := ⟨Y.sc, eEK + 1152, 32⟩) (by sc_decide), Buf.addr_eq hp (b := bEK Y.sc) (by sc_decide),
    BitVec.add_assoc, ← BitVec.ofNat_add]

theorem seed_split (hS : SOK Y) {s₀ : State} (hp : TPre Y s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (bSeed Y.sc)) 34 = bytesAt m (Buf.addr s₀ ⟨Y.sc, eEK + 1152, 32⟩) 32 ++
      (bytesAt m (Buf.addr s₀ ⟨Y.sc, eEK + 1184, 1⟩) 1 ++ bytesAt m (Buf.addr s₀ ⟨Y.sc, eEK + 1185, 1⟩) 1) := by
  rw [bytes_split hp m (o' := eEK + 1184) (l₁ := 32) (l₂ := 2) rfl rfl (by sc_decide) (by sc_decide),
    bytes_split hp m (a := Y.sc) (o := eEK + 1184) (o' := eEK + 1185) (l₁ := 1) (l₂ := 1) rfl rfl
      (by sc_decide) (by sc_decide)]

theorem mSE_eq (I : Inp) (s₀ : State) {i j : Nat} (hj : j < 3) : mSE I s₀ (3 * i + j) = matSeed (ρE I s₀) j i := by
  simp only [mSE]
  rw [show (3 * i + j) % 3 = j by omega, show (3 * i + j) / 3 = i by omega]

/-! ## An entry -/

/-- After `i` is stored. -/
structure S1 (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends R Y I i j s₀ s where
  bi : bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, eEK + 1184, 1⟩) 1 = [BitVec.ofNat 8 i]

/-- After `ρ ‖ i ‖ j` is stored. -/
structure S2 (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends R Y I i j s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (bSeed Y.sc)) 34 = matSeed (ρE I s₀) j i

/-- After `Â[j, i]` is sampled, `r` returned. -/
structure S3 (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends R Y I i j s₀ s where
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (bA Y.sc))
  out : Outcome (fun iters => sampleNTT iters (matSeed (ρE I s₀) j i)) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (bA Y.sc)))

/-- After it is masked, and `eACC` updated. -/
structure S4 (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends B Y I (3 * i + j + 1) i s₀ s where
  u : 0 < j → Reduced s.mem (Buf.addr s₀ (bU Y.sc)) ∧
    (accE Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU Y.sc)) = partU I s₀ i j)
  red : Reduced s.mem (Buf.addr s₀ (bA Y.sc))
  a : accE Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bA Y.sc)) = aE I s₀ j i

theorem safe_ent (hS : SOK Y) :
    safe Y [⟨Y.sc, eEK + 1184, 1⟩] = true ∧ safe Y [⟨Y.sc, eEK + 1185, 1⟩] = true ∧
    Y.apart (bU Y.sc) [⟨Y.sc, eEK + 1184, 1⟩] = true ∧ Y.apart (bU Y.sc) [⟨Y.sc, eEK + 1185, 1⟩] = true ∧
    Y.apart ⟨Y.sc, eEK + 1184, 1⟩ [⟨Y.sc, eEK + 1185, 1⟩] = true ∧
    safe Y [bA Y.sc, bSS Y.sc] = true ∧ Y.apart (bU Y.sc) [bA Y.sc, bSS Y.sc] = true ∧
    safeS Y [bACC Y.sc, bA Y.sc] = true ∧ (∀ i < 3, Y.apart (bCU Y.sc i) [bACC Y.sc, bA Y.sc] = true) ∧
    Y.apart (bU Y.sc) [bACC Y.sc, bA Y.sc] = true := by
  sc_decide'

/-- `ρ ‖ i ‖ j`, `Â[j, i]` sampled and masked, then `c`. -/
theorem sample_piece (hS : SOK Y) {I : Inp} (hρ : RhoPub Y lk I) (i j : Nat) (hi : i < 3) (hj : j < 3)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (eEK + 1184) i)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (eEK + 1185) j)) h₂).isSome = true)
    {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (S4 Y I i j) Q c) :
    Piece (TPre Y) (TPub Y lk) (R Y I i j) Q
      (.seq (.block (st8 (eEK + 1184) i)) <| .seq (.block (st8 (eEK + 1185) j)) <|
        .seq (sampleC Y.sc (bSeed Y.sc) (bA Y.sc) (bSS Y.sc)) (.seq (maskA eACC eA) c)) := by
  obtain ⟨n₁, n₂, n₃, n₄, n₅, p₁, p₂, q₁, q₂, q₃⟩ := safe_ent hS
  have k88 : 0 + 16 ≤ Y.stk := hS.le
  refine Piece.seq (B := S1 Y I i j) (st8_piece (Y := Y) (eEK + 1184) i (by sc_decide) t₁
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hi hp k88 n₁ n₃ (m' ▸ frW8) h', by rw [m']; exact st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := S2 Y I i j) (st8_piece (Y := Y) (eEK + 1185) j (by sc_decide) t₂
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ?_) ?_
  · have k := h.keep hi hp k88 n₂ n₄ (m' ▸ frW8) h'
    refine ⟨k, ?_⟩
    rw [seed_split hS hp, rho_eq hS hp k.toBase, keepBytes hp k88 n₅ (m' ▸ frW8), h.bi, m', st8_byte]
    rfl
  refine Piece.seq (B := S3 Y I i j) (sampleC_piece (Y := Y) Y.sc (eEK + 1152) Y.sc eA Y.sc eSS (by sc_decide)
    hS.le (by sc_taint) (fun _ _ _ h => h.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => ?_)
    fun s₀ s s' hp h h' fr red out => ⟨h.keep hi hp hS.le p₁ p₂ fr h', red, ?_⟩) ?_
  · rw [h.seed, h'.seed, hρ s₀ s₀' hp hp' hq]
  · rw [h.seed] at out; exact out
  refine Piece.seq (maskA_piece (Y := Y) eACC eA (by sc_decide) (by sc_taint) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_) hc
  have fr' := fr2 fr
  have hr := outcome_01 h.out
  have ea : accE Y s₀ s' = accE Y s₀ s &&& s.gpr .eax := ha
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
    · refine ⟨3 * i + j, by omega, ?_⟩
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
structure S5 (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends S4 Y I i j s₀ s where
  p : Reduced s.mem (Buf.addr s₀ (bP Y.sc)) ∧
    (accE Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bP Y.sc)) = multiplyNTTs (aE I s₀ j i) (yE I s₀ j))

theorem safe_mul (hS : SOK Y) : safe Y [bU Y.sc, bNS Y.sc] = true ∧ safe Y [bP Y.sc, bNS Y.sc] = true ∧
    safe Y [bU Y.sc] = true ∧ Y.apart (bU Y.sc) [bP Y.sc, bNS Y.sc] = true ∧
    Y.apart (bA Y.sc) [bP Y.sc, bNS Y.sc] = true ∧ Y.apart (bACC Y.sc) [bU Y.sc, bNS Y.sc] = true ∧
    Y.apart (bACC Y.sc) [bP Y.sc, bNS Y.sc] = true ∧ Y.apart (bACC Y.sc) [bU Y.sc] = true ∧
    (Y.okW (bU Y.sc) && Y.ok (bA Y.sc) && Y.ok (bY Y.sc 0) && Y.okW (bNS Y.sc) && Y.sep (bU Y.sc) (bA Y.sc) &&
      Y.sep (bU Y.sc) (bY Y.sc 0) && Y.sep (bU Y.sc) (bNS Y.sc) && Y.sep (bA Y.sc) (bNS Y.sc) &&
      Y.sep (bY Y.sc 0) (bNS Y.sc)) = true ∧
    (∀ j < 3, (Y.okW (bP Y.sc) && Y.ok (bA Y.sc) && Y.ok (bY Y.sc j) && Y.okW (bNS Y.sc) &&
      Y.sep (bP Y.sc) (bA Y.sc) && Y.sep (bP Y.sc) (bY Y.sc j) && Y.sep (bP Y.sc) (bNS Y.sc) &&
      Y.sep (bA Y.sc) (bNS Y.sc) && Y.sep (bY Y.sc j) (bNS Y.sc)) = true) ∧
    (Y.okW (bU Y.sc) && Y.ok (bP Y.sc) && Y.sep (bU Y.sc) (bP Y.sc)) = true := by
  sc_decide'

/-- Entry `(i, 0)`: `u[i] ← Â[0, i] ×_T ŷ[0]`. -/
theorem entry0_piece (hS : SOK Y) {I : Inp} (hρ : RhoPub Y lk I) (i : Nat) (hi : i < 3)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (eEK + 1184) i)) h₁).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (R Y I i 0) (R Y I i 1) (encEntry Y.sc i 0) := by
  obtain ⟨m₁, -, -, -, -, a₁, -, -, o₁, -, -⟩ := safe_mul hS
  refine sample_piece hS hρ i 0 hi (by decide) t₁ (by sc_taint) (mulC_piece (Y := Y) Y.sc eU Y.sc eA Y.sc 0 Y.sc eNS
    o₁ hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.y 0 (by decide)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  have k := h.toB.keep hp hS.le m₁ (by omega) fr h'
  have ea : accE Y s₀ s' = accE Y s₀ s := keepW hp hS.le a₁ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, h.a (ea ▸ e₁), (h.y 0 (by decide)).2]
  rfl

/-- Entry `(i, j + 1)`: `u[i] ← u[i] + Â[j + 1, i] ×_T ŷ[j + 1]`. -/
theorem entry_piece (hS : SOK Y) {I : Inp} (hρ : RhoPub Y lk I) (i j : Nat) (hi : i < 3) (hj : j + 1 < 3)
    {h₁ h₂ h₃ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (eEK + 1184) i)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (eEK + 1185) (j + 1))) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax (bP Y.sc) ++ ptrTo Y.sc .ecx (bA Y.sc) ++
      ptrTo Y.sc .edx (bY Y.sc (j + 1)) ++ ptrTo Y.sc .edi (bNS Y.sc))) h₃).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (R Y I i (j + 1)) (R Y I i (j + 2)) (encEntry Y.sc i (j + 1)) := by
  obtain ⟨-, m₂, m₃, m₄, m₅, -, a₂, a₃, -, o₂, o₃⟩ := safe_mul hS
  refine sample_piece hS hρ i (j + 1) hi hj t₁ t₂ (.seq (B := S5 Y I i (j + 1))
    (mulC_piece (Y := Y) Y.sc eP Y.sc eA Y.sc (1024 * (j + 1)) Y.sc eNS (o₂ (j + 1) hj) hS.le t₃
      (fun _ _ _ h => ⟨h.ctx, h.red, (h.y (j + 1) (by omega)).1⟩) fun s₀ s s' hp h h' fr post => ?_) ?_)
  · have k := h.toB.keep hp hS.le m₂ (by omega) fr h'
    have ea : accE Y s₀ s' = accE Y s₀ s := keepW hp hS.le a₂ fr
    refine ⟨⟨k, fun hj' => ⟨keepRed hp hS.le m₄ fr (h.u hj').1, fun e₁ => ?_⟩,
      keepRed hp hS.le m₅ fr h.red, fun e₁ => ?_⟩, post.1, fun e₁ => ?_⟩
    · rw [polyAt_congr (Top.keep hp hS.le m₄ fr)]; exact (h.u hj').2 (ea ▸ e₁)
    · rw [polyAt_congr (Top.keep hp hS.le m₅ fr)]; exact h.a (ea ▸ e₁)
    · rw [post.2, h.a (ea ▸ e₁), (h.y (j + 1) (by omega)).2]
  refine accC_piece add_verified add_nosp add_stack Y.sc eU Y.sc eP o₃ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.u (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.toB.keep hp hS.le m₃ (by omega) fr h'
  have ea : accE Y s₀ s' = accE Y s₀ s := keepW hp hS.le a₃ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, (h.u (Nat.succ_pos _)).2 (ea ▸ e₁), h.p.2 (ea ▸ e₁)]
  rfl

end VG.Proof.MlKem.X86.Enc
