import VerifiedGarbage.Proof.MlKem.X86.KeyGenPrf
import VerifiedGarbage.Proof.MlKem.X86.TopSeq2

/-!
# ML-KEM-768 on x86 (32-bit): `t̂` in `vg_mlkem768_keygen`

Untrusted: everything here is checked by Lean. Row `i` of `Â` (`kgRow i`):
each entry `Â[i, j]` is sampled from `ρ ‖ j ‖ i`, masked by the value
`vg_mlkem_sample_ntt` returned, which is ANDed into `kgACC`
(`entry0_piece`, `entry_piece`), and multiplied by `ŝ[j]` into `t̂[i]`; then
`ê[i]` is added and `t̂[i]` encoded into `ek` (`row_piece`).

`B k e` is what holds after `k` entries and `e` rows: `kgACC` is 0 or 1; if
1, the first `k` samples succeeded, and the first `e` rows of `ek` are those
of `ek_PKE` for the matrix `aM` they sampled; if 0, one of the nine samples
failed within `minIterations` iterations.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Row `i` of `ek`. -/
abbrev bEK (i : Nat) : Buf := ⟨1, 384 * i, 384⟩

section
variable (s₀ : State)
/-- The seed of the `k`th entry of `Â`, `Â[k / 3, k % 3]`. -/
abbrev mS (k : Nat) : List Byte := matSeed (kgRho (d s₀)) (k / 3) (k % 3)
/-- `Â[i, j]`, if sampled. -/
noncomputable abbrev aM (i j : Nat) : Poly := sv (matSeed (kgRho (d s₀)) i j)

/-- `Â[i, 0] ×_T ŝ[0] + … + Â[i, j - 1] ×_T ŝ[j - 1]`, for `0 < j`. -/
noncomputable def part (i : Nat) : Nat → Poly
  | 0 => zero
  | 1 => multiplyNTTs (aM s₀ i 0) (seP s₀ 0)
  | j + 1 => add (part i j) (multiplyNTTs (aM s₀ i j) (seP s₀ j))
end

/-- `kgACC`. -/
abbrev accV (s₀ s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ bACC) 32

/-- See the module documentation. -/
structure B (k e : Nat) (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ bRho) 32 = kgRho (d s₀)
  se : ∀ j < 6, PolyIs s.mem (Buf.addr s₀ (bSE j)) (seP s₀ j)
  acc : accV s₀ s = 0 ∨ accV s₀ s = 1
  ok : accV s₀ s = 1 → ∀ k' < k, ∃ a, Samp (mS s₀ k') a
  fail : accV s₀ s = 0 → ∃ k' < 9, sampleNTT minIterations (mS s₀ k') = none
  ek : accV s₀ s = 1 → ∀ i < e, bytesAt s.mem (Buf.addr s₀ (bEK i)) 384 = encode12 (kgT (aM s₀) (d s₀) i)

/-- Whether `bs` is apart from `ρ`, `ŝ` and `ê`. -/
def safeS (bs : List Buf) : Bool := Y.apart bRho bs && (List.range 6).all fun j => Y.apart (bSE j) bs

/-- Whether `bs` is also apart from `kgACC` and `ek`. -/
def safe (bs : List Buf) : Bool :=
  Y.apart bACC bs && safeS bs && (List.range 3).all fun i => Y.apart (bEK i) bs

/-- What `B` states of `ρ`, `ŝ` and `ê`, kept. -/
theorem keepS {s₀ : State} {m m' : Mem} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : safeS bs = true) (fr : Frame (FR s₀ bs M) m m')
    (h₁ : bytesAt m (Buf.addr s₀ bRho) 32 = kgRho (d s₀)) (h₂ : ∀ j < 6, PolyIs m (Buf.addr s₀ (bSE j)) (seP s₀ j)) :
    bytesAt m' (Buf.addr s₀ bRho) 32 = kgRho (d s₀) ∧ ∀ j < 6, PolyIs m' (Buf.addr s₀ (bSE j)) (seP s₀ j) := by
  simp only [safeS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  exact ⟨by rw [keepBytes hp hM hs.1 fr]; exact h₁, fun j hj => keepPoly hp hM (hs.2 j hj) fr (h₂ j hj)⟩

theorem B.keep {k e : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : safe bs = true) (he : e ≤ 3)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : B k e s₀ s) (c : Ctx Y s₀ s') : B k e s₀ s' := by
  simp only [safe, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hs
  have ea : accV s₀ s' = accV s₀ s := keepW hp hM h₁ fr
  obtain ⟨k₁, k₂⟩ := keepS hp hM h₂ fr h.rho h.se
  refine ⟨c, k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i hi => ?_⟩
  rw [keepBytes hp hM (h₃ i (by omega)) fr]
  exact h.ek (ea ▸ e₁) i hi

/-- Before entry `(i, j)`: and `t̂[i]` so far, if `0 < j`. -/
structure R (i j : Nat) (s₀ s : State) : Prop extends B (3 * i + j) i s₀ s where
  t : 0 < j → Reduced s.mem (Buf.addr s₀ bT) ∧ (accV s₀ s = 1 → polyAt s.mem (Buf.addr s₀ bT) = part s₀ i j)

theorem R.keep {i j : Nat} (hi : i < 3) {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (hs : safe bs = true) (hT : Y.apart bT bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : R i j s₀ s) (c : Ctx Y s₀ s') : R i j s₀ s' := by
  have k := h.toB.keep hp hM hs (by omega) fr c
  have ea : accV s₀ s' = accV s₀ s := keepW hp hM (by simp only [safe, Bool.and_eq_true] at hs; exact hs.1.1) fr
  refine ⟨k, fun hj => ⟨keepRed hp hM hT fr (h.t hj).1, fun e₁ => ?_⟩⟩
  rw [polyAt_congr (Top.keep hp hM hT fr)]
  exact (h.t hj).2 (ea ▸ e₁)

/-! ## Bytes -/

theorem st8_byte {s₀ : State} (m : Mem) (o v : Nat) :
    bytesAt (m.writeW (Buf.addr s₀ ⟨Y.sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8)) (Buf.addr s₀ ⟨3, o, 1⟩) 1 =
      [BitVec.ofNat 8 v] := by
  refine bytesAt_eq (L := [BitVec.ofNat 8 v]) rfl fun i hi => ?_
  obtain rfl : i = 0 := by omega
  simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero]
  refine (ite_eq_left (rfl : Buf.addr s₀ ⟨3, o, 1⟩ = Buf.addr s₀ ⟨Y.sc, o, 1⟩)).trans ?_
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

/-- `ρ ‖ j ‖ i`, the seed of `Â[i, j]`. -/
abbrev bSeed : Buf := ⟨3, kgRS, 34⟩
abbrev bJ : Buf := ⟨3, kgRS + 32, 1⟩
abbrev bI : Buf := ⟨3, kgRS + 33, 1⟩

theorem seed_split {s₀ : State} (hp : TPre Y s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ bSeed) 34 =
      bytesAt m (Buf.addr s₀ bRho) 32 ++ (bytesAt m (Buf.addr s₀ bJ) 1 ++ bytesAt m (Buf.addr s₀ bI) 1) := by
  have e₁ : Buf.addr s₀ bJ = Buf.addr s₀ bRho + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := bJ) (by decide), Buf.addr_eq hp (b := bRho) (by decide), BitVec.add_assoc,
      ← BitVec.ofNat_add]
  have e₂ : Buf.addr s₀ bI = Buf.addr s₀ bJ + BitVec.ofNat 64 1 := by
    rw [Buf.addr_eq hp (b := bJ) (by decide), Buf.addr_eq hp (b := bI) (by decide), BitVec.add_assoc,
      ← BitVec.ofNat_add]
  rw [e₂, e₁, ← bytesAt_add, show Buf.addr s₀ bSeed = Buf.addr s₀ bRho from rfl]
  exact bytesAt_add m _ 32 2

/-! ## The value returned by `SampleNTT`, and `kgACC` -/

theorem mS_eq (s₀ : State) {i j : Nat} (hj : j < 3) : mS s₀ (3 * i + j) = matSeed (kgRho (d s₀)) i j := by
  simp only [mS]
  rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega]

/-! ## An entry -/

/-- After `ρ ‖ j` is stored. -/
structure S1 (i j : Nat) (s₀ s : State) : Prop extends R i j s₀ s where
  bj : bytesAt s.mem (Buf.addr s₀ bJ) 1 = [BitVec.ofNat 8 j]

/-- After `ρ ‖ j ‖ i` is stored. -/
structure S2 (i j : Nat) (s₀ s : State) : Prop extends R i j s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ bSeed) 34 = matSeed (kgRho (d s₀)) i j

/-- After `Â[i, j]` is sampled, `r` returned. -/
structure S3 (i j : Nat) (s₀ s : State) : Prop extends R i j s₀ s where
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ bA)
  out : Outcome (fun iters => sampleNTT iters (matSeed (kgRho (d s₀)) i j)) (s.gpr .eax) (polyAt s.mem (Buf.addr s₀ bA))

/-- After it is masked, and `kgACC` updated. -/
structure S4 (i j : Nat) (s₀ s : State) : Prop extends B (3 * i + j + 1) i s₀ s where
  t : 0 < j → Reduced s.mem (Buf.addr s₀ bT) ∧ (accV s₀ s = 1 → polyAt s.mem (Buf.addr s₀ bT) = part s₀ i j)
  red : Reduced s.mem (Buf.addr s₀ bA)
  a : accV s₀ s = 1 → polyAt s.mem (Buf.addr s₀ bA) = aM s₀ i j

theorem safe_nb : safe [⟨Y.sc, kgRS + 32, 1⟩] = true ∧ safe [⟨Y.sc, kgRS + 33, 1⟩] = true ∧
    Y.apart bT [⟨Y.sc, kgRS + 32, 1⟩] = true ∧ Y.apart bT [⟨Y.sc, kgRS + 33, 1⟩] = true ∧
    Y.apart bJ [⟨Y.sc, kgRS + 33, 1⟩] = true := by decide
theorem safe_samp : safe [bA, bSS] = true ∧ Y.apart bT [bA, bSS] = true := by decide
theorem safe_mask : safeS [bACC, bA] = true ∧ (∀ i < 3, Y.apart (bEK i) [bACC, bA] = true) ∧
    Y.apart bT [bACC, bA] = true := by decide
theorem safe_mul : safe [bT, bNS] = true ∧ safe [bP, bNS] = true ∧ safe [bT] = true ∧
    Y.apart bT [bP, bNS] = true ∧ Y.apart bA [bP, bNS] = true := by decide
theorem ok_mul0 : (Y.okW bT && Y.ok bA && Y.ok (bSE 0) && Y.okW bNS && Y.sep bT bA && Y.sep bT (bSE 0) &&
    Y.sep bT bNS && Y.sep bA bNS && Y.sep (bSE 0) bNS) = true := by decide
theorem ok_mul : ∀ j < 3, (Y.okW bP && Y.ok bA && Y.ok (bSE j) && Y.okW bNS && Y.sep bP bA &&
    Y.sep bP (bSE j) && Y.sep bP bNS && Y.sep bA bNS && Y.sep (bSE j) bNS) = true := by decide

/-- `ρ ‖ j ‖ i`, `Â[i, j]` sampled and masked, then `c`. -/
theorem sample_piece (i j : Nat) (hi : i < 3) (hj : j < 3) {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (kgRS + 32) j)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (kgRS + 33) i)) h₂).isSome = true)
    {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (S4 i j) Q c) :
    Piece (TPre Y) (TPub Y lk) (R i j) Q
      (.seq (.block (st8 (kgRS + 32) j)) <| .seq (.block (st8 (kgRS + 33) i)) <|
        .seq (sampleC 3 ⟨3, kgRS, 34⟩ ⟨3, kgA, 1024⟩ ⟨3, kgSS, 2048⟩) (.seq (maskA kgACC kgA) c)) := by
  obtain ⟨n₁, n₂, n₃, n₄, n₅⟩ := safe_nb
  refine Piece.seq (B := S1 i j) (st8_piece (Y := Y) (kgRS + 32) j (by decide) t₁
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hi hp (M := 0) (by decide) n₁ n₃ (m' ▸ frW8) h', by rw [m']; exact st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := S2 i j) (st8_piece (Y := Y) (kgRS + 33) i (by decide) t₂
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ?_) ?_
  · have k := h.keep hi hp (M := 0) (by decide) n₂ n₄ (m' ▸ frW8) h'
    refine ⟨k, ?_⟩
    rw [seed_split hp, k.rho, keepBytes hp (N := 0) (by decide) n₅ (m' ▸ frW8), h.bj, m', st8_byte]
    rfl
  obtain ⟨p₁, p₂⟩ := safe_samp
  refine Piece.seq (B := S3 i j) (sampleC_piece (Y := Y) 3 kgRS 3 kgA 3 kgSS (by decide) (by decide)
    (by taint_decide) (fun _ _ _ h => h.ctx) (fun s₀ s₀' s s' _ _ hq h h' => ?_)
    fun s₀ s s' hp h h' fr red out => ⟨h.keep hi hp (by decide) p₁ p₂ fr h', red, ?_⟩) ?_
  · rw [h.seed, h'.seed]; exact congrArg (matSeed · i j) hq.2.2
  · rw [h.seed] at out; exact out
  obtain ⟨q₁, q₂, q₃⟩ := safe_mask
  refine Piece.seq (maskA_piece (Y := Y) kgACC kgA (by decide) (by taint_decide) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_) hc
  have fr' := fr2 fr
  have hr := outcome_01 h.out
  obtain ⟨s₁, s₂, s₃⟩ := acc_step h.acc hr
  have ea : accV s₀ s' = accV s₀ s &&& s.gpr .eax := ha
  rw [← ea] at s₁ s₂ s₃
  obtain ⟨k₁, k₂⟩ := keepS hp (M := 0) (by decide) q₁ fr' h.rho h.se
  obtain ⟨mr, ma⟩ := mask_poly hr hc h.red
  refine ⟨⟨h', k₁, k₂, s₁, fun e₁ k' hk' => ?_, fun e₁ => ?_, fun e₁ i' hi' => ?_⟩,
    fun hj => ⟨keepRed hp (by decide) q₃ fr' (h.t hj).1, fun e₁ => ?_⟩, mr, fun e₁ => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · exact h.ok (s₂ e₁).1 k' hk'
    · rw [mS_eq s₀ hj]
      rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
      · exact ⟨_, it, e⟩
      · exact absurd ((s₂ e₁).2) (by rw [e]; decide)
  · rcases s₃ e₁ with e₂ | e₂
    · exact h.fail e₂
    · refine ⟨3 * i + j, by omega, ?_⟩
      rw [mS_eq s₀ hj]
      rcases h.out with ⟨e, _⟩ | ⟨_, e⟩
      · exact absurd e (by rw [e₂]; decide)
      · exact e
  · rw [keepBytes hp (N := 0) (by decide) (q₂ i' (by omega)) fr']
    exact h.ek (s₂ e₁).1 i' hi'
  · rw [polyAt_congr (Top.keep hp (by decide) q₃ fr')]
    exact (h.t hj).2 (s₂ e₁).1
  · refine (ma (s₂ e₁).2).trans ?_
    rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
    · exact (sv_eq ⟨it, e⟩).symm
    · exact absurd ((s₂ e₁).2) (by rw [e]; decide)

/-- After `Â[i, j] ×_T ŝ[j]` is computed, for `0 < j`. -/
structure S5 (i j : Nat) (s₀ s : State) : Prop extends S4 i j s₀ s where
  p : Reduced s.mem (Buf.addr s₀ bP) ∧
    (accV s₀ s = 1 → polyAt s.mem (Buf.addr s₀ bP) = multiplyNTTs (aM s₀ i j) (seP s₀ j))

/-- Entry `(i, 0)`: `t̂[i] ← Â[i, 0] ×_T ŝ[0]`. -/
theorem entry0_piece (i : Nat) (hi : i < 3) {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (kgRS + 33) i)) h₂).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (R i 0) (R i 1) (kgEntry i 0) := by
  obtain ⟨m₁, -, -, -, -⟩ := safe_mul
  refine sample_piece i 0 hi (by decide) (by taint_decide) t₂ (mulC_piece (Y := Y) 3 Impl.MlKem.X86.kgT 3 kgA 3 0 3 kgNS ok_mul0
    (by decide) (by taint_decide) (fun _ _ _ h => ⟨h.ctx, h.red, (h.se 0 (by decide)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  have k := h.toB.keep hp (by decide) m₁ (by omega) fr h'
  have ea : accV s₀ s' = accV s₀ s := keepW hp (by decide) (by decide) fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, h.a (ea ▸ e₁), (h.se 0 (by decide)).2]
  rfl

/-- Entry `(i, j + 1)`: `t̂[i] ← t̂[i] + Â[i, j + 1] ×_T ŝ[j + 1]`. -/
theorem entry_piece (i j : Nat) (hi : i < 3) (hj : j + 1 < 3) {h₁ h₂ h₃ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (kgRS + 32) (j + 1))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (kgRS + 33) i)) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax bP ++ ptrTo Y.sc .ecx bA ++
      ptrTo Y.sc .edx (bSE (j + 1)) ++ ptrTo Y.sc .edi bNS)) h₃).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (R i (j + 1)) (R i (j + 2)) (kgEntry i (j + 1)) := by
  obtain ⟨-, m₂, m₃, m₄, m₅⟩ := safe_mul
  refine sample_piece i (j + 1) hi hj t₁ t₂ (.seq (B := S5 i (j + 1))
    (mulC_piece (Y := Y) 3 kgP 3 kgA 3 (1024 * (j + 1)) 3 kgNS (ok_mul (j + 1) hj) (by decide) t₃
      (fun _ _ _ h => ⟨h.ctx, h.red, (h.se (j + 1) (by omega)).1⟩) fun s₀ s s' hp h h' fr post => ?_) ?_)
  · have k := h.toB.keep hp (by decide) m₂ (by omega) fr h'
    have ea : accV s₀ s' = accV s₀ s := keepW hp (by decide) (by decide) fr
    refine ⟨⟨k, fun hj' => ⟨keepRed hp (by decide) m₄ fr (h.t hj').1, fun e₁ => ?_⟩,
      keepRed hp (by decide) m₅ fr h.red, fun e₁ => ?_⟩, post.1, fun e₁ => ?_⟩
    · rw [polyAt_congr (Top.keep hp (by decide) m₄ fr)]; exact (h.t hj').2 (ea ▸ e₁)
    · rw [polyAt_congr (Top.keep hp (by decide) m₅ fr)]; exact h.a (ea ▸ e₁)
    · rw [post.2, h.a (ea ▸ e₁), (h.se (j + 1) (by omega)).2]
  refine accC_piece add_verified add_nosp add_stack 3 Impl.MlKem.X86.kgT 3 kgP (by decide) (by decide) (by taint_decide)
    (fun _ _ _ h => ⟨h.ctx, (h.t (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.toB.keep hp (by decide) m₃ (by omega) fr h'
  have ea : accV s₀ s' = accV s₀ s := keepW hp (by decide) (by decide) fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, (h.t (Nat.succ_pos _)).2 (ea ▸ e₁), h.p.2 (ea ▸ e₁)]
  rfl

/-! ## A row -/

/-- `t̂[i]` is computed. -/
structure S6 (i : Nat) (s₀ s : State) : Prop extends B (3 * i + 3) i s₀ s where
  t : Reduced s.mem (Buf.addr s₀ bT) ∧ (accV s₀ s = 1 → polyAt s.mem (Buf.addr s₀ bT) = kgT (aM s₀) (d s₀) i)

theorem ok_row : ∀ i < 3, (Y.okW bT && Y.ok (bSE (3 + i)) && Y.sep bT (bSE (3 + i))) = true ∧
    (Y.ok bT && Y.okW (bEK i) && Y.sep bT (bEK i)) = true ∧ safeS [bEK i] = true ∧
    Y.apart bACC [bEK i] = true ∧ ∀ i' < i, Y.apart (bEK i') [bEK i] = true := by decide

/-- Row `i`: `t̂[i] = Â[i] ∘ ŝ + ê[i]`, encoded into `ek`. -/
theorem row_piece (i : Nat) (hi : i < 3) {h₂ h₄ h₅ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (kgRS + 33) i)) h₂).isSome = true)
    (t₄ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax bT ++ ptrTo Y.sc .ecx (bSE (3 + i)))) h₄).isSome = true)
    (t₅ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax bT ++ ptrTo Y.sc .ecx (bEK i))) h₅).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (B (3 * i) i) (B (3 * i + 3) (i + 1)) (kgRow i) := by
  obtain ⟨o₁, o₂, o₃, o₄, o₅⟩ := ok_row i hi
  obtain ⟨-, -, m₃, -, -⟩ := safe_mul
  refine Piece.seq (entry0_piece i hi t₂ |>.mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h) ?_
  refine Piece.seq (entry_piece i 0 hi (by decide) (by taint_decide) t₂ (by taint_decide)) ?_
  refine Piece.seq (entry_piece i 1 hi (by decide) (by taint_decide) t₂ (by taint_decide)) ?_
  refine Piece.seq (B := S6 i) (accC_piece add_verified add_nosp add_stack 3 Impl.MlKem.X86.kgT 3 (1024 * (3 + i))
    o₁ (by decide) t₄ (fun _ _ _ h => ⟨h.ctx, (h.t (by decide)).1, (h.se (3 + i) (by omega)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.toB.keep hp (by decide) m₃ (by omega) fr h'
    have ea : accV s₀ s' = accV s₀ s := keepW hp (by decide) (by decide) fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, (h.t (by decide)).2 (ea ▸ e₁), (h.se (3 + i) (by omega)).2]
    rfl
  refine enc12C_piece (Y := Y) 3 Impl.MlKem.X86.kgT 1 (384 * i) o₂ (by decide) t₅ (fun _ _ _ h => ⟨h.ctx, h.t.1⟩)
    fun s₀ s s' hp h h' fr post => ?_
  obtain ⟨k₁, k₂⟩ := keepS hp (by decide) o₃ fr h.rho h.se
  have ea : accV s₀ s' = accV s₀ s := keepW hp (by decide) o₄ fr
  refine ⟨h', k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i' hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
  · rw [keepBytes hp (by decide) (o₅ i' hi') fr]; exact h.ek (ea ▸ e₁) i' hi'
  · rw [post, h.t.2 (ea ▸ e₁)]

/-- The three rows, then `c`. -/
theorem rows_piece {Q : State → State → Prop} {c : Prog isa} (h : Piece (TPre Y) (TPub Y lk) (B 9 3) Q c) :
    Piece (TPre Y) (TPub Y lk) (B 0 0) Q (.seq (kgRow 0) <| .seq (kgRow 1) <| .seq (kgRow 2) c) :=
  .seq (row_piece 0 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) <|
  .seq (row_piece 1 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) <|
  .seq (row_piece 2 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) h

end VG.Proof.MlKem.X86.KeyGen
