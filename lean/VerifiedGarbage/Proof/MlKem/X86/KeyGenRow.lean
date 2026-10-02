import VerifiedGarbage.Proof.MlKem.X86.KeyGenPrf
import VerifiedGarbage.Proof.MlKem.X86.TopSeq2

/-!
# ML-KEM on x86 (32-bit): `t̂` in key generation

Row `i` of `Â` (`kgRow L i`): each entry `Â[i, j]` is sampled from `ρ ‖ j ‖ i`,
masked by the value `vg_mlkem_sample_ntt` returned, which is ANDed into
`kgACC` (`entry0_piece`, `entry_piece`), and multiplied by `ŝ[j]` into
`t̂[i]`; then `ê[i]` is added and `t̂[i]` encoded into `ek` (`row_piece`).

`B k e` is what holds after `k` entries and `e` rows: `kgACC` is 0 or 1; if
1, the first `k` samples succeeded, and the first `e` rows of `ek` are those
of `ek_PKE` for the matrix `aM` they sampled; if 0, one of the `k²` samples
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
variable (L : KemLay) (s₀ : State)
/-- The seed of the `k`th entry of `Â`, `Â[k / k, k % k]`. -/
abbrev mS (k : Nat) : List Byte := matSeed (KPke.kgRho L.p (d s₀)) (k / L.p.k) (k % L.p.k)
/-- `Â[i, j]`, if sampled. -/
noncomputable abbrev aM (i j : Nat) : Poly := sv (matSeed (KPke.kgRho L.p (d s₀)) i j)

/-- `Â[i, 0] ×_T ŝ[0] + … + Â[i, j - 1] ×_T ŝ[j - 1]`. -/
noncomputable abbrev part (i j : Nat) : Poly := KPke.dotK (aM L s₀ i) (seP L s₀) j
end

/-- `kgACC`. -/
abbrev accV (L : KemLay) (s₀ s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (bACC L)) 32

/-- See the module documentation. -/
structure B (L : KemLay) (k e : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ (bRho L)) 32 = KPke.kgRho L.p (d s₀)
  se : ∀ j < 2 * L.p.k, PolyIs s.mem (Buf.addr s₀ (bSE j)) (seP L s₀ j)
  acc : accV L s₀ s = 0 ∨ accV L s₀ s = 1
  ok : accV L s₀ s = 1 → ∀ k' < k, ∃ a, Samp (mS L s₀ k') a
  fail : accV L s₀ s = 0 → ∃ k' < L.p.k * L.p.k, sampleNTT minIterations (mS L s₀ k') = none
  ek : accV L s₀ s = 1 → ∀ i < e,
    bytesAt s.mem (Buf.addr s₀ (bEK i)) 384 = encode12 (KPke.kgT L.p (aM L s₀) (d s₀) i)

/-- Whether `bs` is apart from `ρ`, `ŝ` and `ê`. -/
def safeS (L : KemLay) (bs : List Buf) : Bool :=
  (Y L).apart (bRho L) bs && (List.range (2 * L.p.k)).all fun j => (Y L).apart (bSE j) bs

/-- Whether `bs` is also apart from `kgACC` and `ek`. -/
def safe (L : KemLay) (bs : List Buf) : Bool :=
  (Y L).apart (bACC L) bs && safeS L bs && (List.range L.p.k).all fun i => (Y L).apart (bEK i) bs

variable {L : KemLay}

/-- What `B` states of `ρ`, `ŝ` and `ê`, kept. -/
theorem keepS {s₀ : State} {m m' : Mem} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ (Y L).stk)
    (hs : safeS L bs = true) (fr : Frame (FR s₀ bs M) m m')
    (h₁ : bytesAt m (Buf.addr s₀ (bRho L)) 32 = KPke.kgRho L.p (d s₀))
    (h₂ : ∀ j < 2 * L.p.k, PolyIs m (Buf.addr s₀ (bSE j)) (seP L s₀ j)) :
    bytesAt m' (Buf.addr s₀ (bRho L)) 32 = KPke.kgRho L.p (d s₀) ∧
      ∀ j < 2 * L.p.k, PolyIs m' (Buf.addr s₀ (bSE j)) (seP L s₀ j) := by
  simp only [safeS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  exact ⟨by rw [keepBytes hp hM hs.1 fr]; exact h₁, fun j hj => keepPoly hp hM (hs.2 j hj) fr (h₂ j hj)⟩

theorem B.keep {k e : Nat} {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (hs : safe L bs = true) (he : e ≤ L.p.k)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : B L k e s₀ s) (c : Ctx (Y L) s₀ s') : B L k e s₀ s' := by
  simp only [safe, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hs
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp hM h₁ fr
  obtain ⟨k₁, k₂⟩ := keepS hp hM h₂ fr h.rho h.se
  refine ⟨c, k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i hi => ?_⟩
  rw [keepBytes hp hM (h₃ i (by omega)) fr]
  exact h.ek (ea ▸ e₁) i hi

/-- Before entry `(i, j)`: and `t̂[i]` so far, if `0 < j`. -/
structure R (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends B L (L.p.k * i + j) i s₀ s where
  t : 0 < j → Reduced s.mem (Buf.addr s₀ (bT L)) ∧
    (accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bT L)) = part L s₀ i j)

theorem R.keep {i j : Nat} (hi : i < L.p.k) {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (hs : safe L bs = true) (hT : (Y L).apart (bT L) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : R L i j s₀ s) (c : Ctx (Y L) s₀ s') : R L i j s₀ s' := by
  have k := h.toB.keep hp hM hs (by omega) fr c
  have ea : accV L s₀ s' = accV L s₀ s :=
    keepW hp hM (by simp only [safe, Bool.and_eq_true] at hs; exact hs.1.1) fr
  refine ⟨k, fun hj => ⟨keepRed hp hM hT fr (h.t hj).1, fun e₁ => ?_⟩⟩
  rw [polyAt_congr (Top.keep hp hM hT fr)]
  exact (h.t hj).2 (ea ▸ e₁)

/-! ## Bytes -/

theorem st8_byte {s₀ : State} (m : Mem) (o v : Nat) :
    bytesAt (m.writeW (Buf.addr s₀ ⟨(Y L).sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8)) (Buf.addr s₀ ⟨3, o, 1⟩) 1 =
      [BitVec.ofNat 8 v] := by
  refine bytesAt_eq (L := [BitVec.ofNat 8 v]) rfl fun i hi => ?_
  obtain rfl : i = 0 := by omega
  simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero]
  refine (ite_eq_left (rfl : Buf.addr s₀ ⟨3, o, 1⟩ = Buf.addr s₀ ⟨(Y L).sc, o, 1⟩)).trans ?_
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

section
variable (L : KemLay)
/-- `ρ ‖ j ‖ i`, the seed of `Â[i, j]`. -/
abbrev bSeed : Buf := ⟨3, L.kgRS, 34⟩
abbrev bJ : Buf := ⟨3, L.kgRS + 32, 1⟩
abbrev bI : Buf := ⟨3, L.kgRS + 33, 1⟩
end

/-- The facts of the layout that the rows use. -/
class KgRowOK (L : KemLay) : Prop where
  seed : (Y L).ok (bJ L) = true ∧ (Y L).ok (bI L) = true ∧ (Y L).ok (bRho L) = true ∧
    (Y L).okW (bJ L) = true ∧ (Y L).okW (bI L) = true
  nb : safe L [⟨3, L.kgRS + 32, 1⟩] = true ∧ safe L [⟨3, L.kgRS + 33, 1⟩] = true ∧
    (Y L).apart (bT L) [⟨3, L.kgRS + 32, 1⟩] = true ∧ (Y L).apart (bT L) [⟨3, L.kgRS + 33, 1⟩] = true ∧
    (Y L).apart (bJ L) [⟨3, L.kgRS + 33, 1⟩] = true
  samp : safe L [bA L, bSS L] = true ∧ (Y L).apart (bT L) [bA L, bSS L] = true ∧
    ((Y L).ok ⟨3, L.kgRS, 34⟩ && (Y L).okW ⟨3, L.kgA, 1024⟩ && (Y L).okW ⟨3, L.kgSS, 2048⟩ &&
      (Y L).sep ⟨3, L.kgRS, 34⟩ ⟨3, L.kgA, 1024⟩ && (Y L).sep ⟨3, L.kgRS, 34⟩ ⟨3, L.kgSS, 2048⟩ &&
      (Y L).sep ⟨3, L.kgA, 1024⟩ ⟨3, L.kgSS, 2048⟩) = true
  mask : safeS L [bACC L, bA L] = true ∧ (∀ i < L.p.k, (Y L).apart (bEK i) [bACC L, bA L] = true) ∧
    (Y L).apart (bT L) [bACC L, bA L] = true ∧
    ((Y L).okW ⟨(Y L).sc, L.kgACC, 4⟩ && (Y L).okW ⟨(Y L).sc, L.kgA, 1024⟩ &&
      (Y L).sep ⟨(Y L).sc, L.kgACC, 4⟩ ⟨(Y L).sc, L.kgA, 1024⟩) = true
  mul : safe L [bT L, bNS L] = true ∧ safe L [bP L, bNS L] = true ∧ safe L [bT L] = true ∧
    (Y L).apart (bT L) [bP L, bNS L] = true ∧ (Y L).apart (bA L) [bP L, bNS L] = true ∧
    (Y L).apart (bACC L) [bT L, bNS L] = true ∧ (Y L).apart (bACC L) [bP L, bNS L] = true ∧
    ((Y L).okW (bT L) && (Y L).ok (bP L) && (Y L).sep (bT L) (bP L)) = true
  mul0 : ((Y L).okW (bT L) && (Y L).ok (bA L) && (Y L).ok (bSE 0) && (Y L).okW (bNS L) &&
    (Y L).sep (bT L) (bA L) && (Y L).sep (bT L) (bSE 0) && (Y L).sep (bT L) (bNS L) && (Y L).sep (bA L) (bNS L) &&
    (Y L).sep (bSE 0) (bNS L)) = true
  mulJ : ∀ j < L.p.k, ((Y L).okW (bP L) && (Y L).ok (bA L) && (Y L).ok (bSE j) && (Y L).okW (bNS L) &&
    (Y L).sep (bP L) (bA L) && (Y L).sep (bP L) (bSE j) && (Y L).sep (bP L) (bNS L) && (Y L).sep (bA L) (bNS L) &&
    (Y L).sep (bSE j) (bNS L)) = true
  row : ∀ i < L.p.k, ((Y L).okW (bT L) && (Y L).ok (bSE (L.p.k + i)) && (Y L).sep (bT L) (bSE (L.p.k + i))) = true ∧
    ((Y L).ok (bT L) && (Y L).okW (bEK i) && (Y L).sep (bT L) (bEK i)) = true ∧ safeS L [bEK i] = true ∧
    (Y L).apart (bACC L) [bEK i] = true ∧ ∀ i' < i, (Y L).apart (bEK i') [bEK i] = true

theorem seed_split [KgRowOK L] {s₀ : State} (hp : TPre (Y L) s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (bSeed L)) 34 =
      bytesAt m (Buf.addr s₀ (bRho L)) 32 ++ (bytesAt m (Buf.addr s₀ (bJ L)) 1 ++ bytesAt m (Buf.addr s₀ (bI L)) 1) := by
  obtain ⟨o₁, o₂, o₃, -⟩ := KgRowOK.seed (L := L)
  have e₁ : Buf.addr s₀ (bJ L) = Buf.addr s₀ (bRho L) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := bJ L) o₁, Buf.addr_eq hp (b := bRho L) o₃, BitVec.add_assoc, ← BitVec.ofNat_add]
  have e₂ : Buf.addr s₀ (bI L) = Buf.addr s₀ (bJ L) + BitVec.ofNat 64 1 := by
    rw [Buf.addr_eq hp (b := bJ L) o₁, Buf.addr_eq hp (b := bI L) o₂, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e₂, e₁, ← bytesAt_add, show Buf.addr s₀ (bSeed L) = Buf.addr s₀ (bRho L) from rfl]
  exact bytesAt_add m _ 32 2

/-! ## The value returned by `SampleNTT`, and `kgACC` -/

theorem mS_eq (s₀ : State) {i j : Nat} (hj : j < L.p.k) : mS L s₀ (L.p.k * i + j) = matSeed (KPke.kgRho L.p (d s₀)) i j := by
  simp only [mS]
  rw [idx_div hj, idx_mod hj]

/-! ## An entry -/

/-- After `ρ ‖ j` is stored. -/
structure S1 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends R L i j s₀ s where
  bj : bytesAt s.mem (Buf.addr s₀ (bJ L)) 1 = [BitVec.ofNat 8 j]

/-- After `ρ ‖ j ‖ i` is stored. -/
structure S2 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends R L i j s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (bSeed L)) 34 = matSeed (KPke.kgRho L.p (d s₀)) i j

/-- After `Â[i, j]` is sampled, `r` returned. -/
structure S3 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends R L i j s₀ s where
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (bA L))
  out : Outcome (fun iters => sampleNTT iters (matSeed (KPke.kgRho L.p (d s₀)) i j)) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (bA L)))

/-- After it is masked, and `kgACC` updated. -/
structure S4 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends B L (L.p.k * i + j + 1) i s₀ s where
  t : 0 < j → Reduced s.mem (Buf.addr s₀ (bT L)) ∧
    (accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bT L)) = part L s₀ i j)
  red : Reduced s.mem (Buf.addr s₀ (bA L))
  a : accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bA L)) = aM L s₀ i j

variable [KgRowOK L]

/-- `ρ ‖ j ‖ i`, `Â[i, j]` sampled and masked, then `c`. -/
theorem sample_piece (i j : Nat) (hi : i < L.p.k) (hj : j < L.p.k) {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (S4 L i j) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (R L i j) Q
      (.seq (.block (st8 (L.kgRS + 32) j)) <| .seq (.block (st8 (L.kgRS + 33) i)) <|
        .seq (sampleC 3 ⟨3, L.kgRS, 34⟩ ⟨3, L.kgA, 1024⟩ ⟨3, L.kgSS, 2048⟩) (.seq (maskA L.kgACC L.kgA) c)) := by
  obtain ⟨n₁, n₂, n₃, n₄, n₅⟩ := KgRowOK.nb (L := L)
  obtain ⟨-, -, -, w₁, w₂⟩ := KgRowOK.seed (L := L)
  refine Piece.seq (B := S1 L i j) (st8_piece (Y := Y L) (L.kgRS + 32) j w₁ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hi hp (M := 0) (by rdecide) n₁ n₃ (m' ▸ frW8 (Y := Y L)) h', by rw [m']; exact st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := S2 L i j) (st8_piece (Y := Y L) (L.kgRS + 33) i w₂ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ?_) ?_
  · have k := h.keep hi hp (M := 0) (by rdecide) n₂ n₄ (m' ▸ frW8 (Y := Y L)) h'
    refine ⟨k, ?_⟩
    rw [seed_split hp, k.rho, keepBytes hp (N := 0) (by rdecide) n₅ (m' ▸ frW8 (Y := Y L)), h.bj, m', st8_byte]
    rfl
  obtain ⟨p₁, p₂, p₃⟩ := KgRowOK.samp (L := L)
  refine Piece.seq (B := S3 L i j) (sampleC_piece (Y := Y L) 3 L.kgRS 3 L.kgA 3 L.kgSS p₃ (by rdecide)
    (by yk_taint) (fun _ _ _ h => h.ctx) (fun s₀ s₀' s s' _ _ hq h h' => ?_)
    fun s₀ s s' hp h h' fr red out => ⟨h.keep hi hp (by rdecide) p₁ p₂ fr h', red, ?_⟩) ?_
  · rw [h.seed, h'.seed]; exact congrArg (matSeed · i j) hq.2.2
  · rw [h.seed] at out; exact out
  obtain ⟨q₁, q₂, q₃, q₄⟩ := KgRowOK.mask (L := L)
  refine Piece.seq (maskA_piece (Y := Y L) L.kgACC L.kgA q₄ (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_) hc
  have fr' := fr2 fr
  have hr := outcome_01 h.out
  obtain ⟨s₁, s₂, s₃⟩ := acc_step h.acc hr
  have ea : accV L s₀ s' = accV L s₀ s &&& s.gpr .eax := ha
  rw [← ea] at s₁ s₂ s₃
  obtain ⟨k₁, k₂⟩ := keepS hp (M := 0) (by rdecide) q₁ fr' h.rho h.se
  obtain ⟨mr, ma⟩ := mask_poly hr hc h.red
  refine ⟨⟨h', k₁, k₂, s₁, fun e₁ k' hk' => ?_, fun e₁ => ?_, fun e₁ i' hi' => ?_⟩,
    fun hj => ⟨keepRed hp (by rdecide) q₃ fr' (h.t hj).1, fun e₁ => ?_⟩, mr, fun e₁ => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · exact h.ok (s₂ e₁).1 k' hk'
    · rw [mS_eq s₀ hj]
      rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
      · exact ⟨_, it, e⟩
      · exact absurd ((s₂ e₁).2) (by rw [e]; decide)
  · rcases s₃ e₁ with e₂ | e₂
    · exact h.fail e₂
    · refine ⟨L.p.k * i + j, idx_lt hi hj, ?_⟩
      rw [mS_eq s₀ hj]
      rcases h.out with ⟨e, _⟩ | ⟨_, e⟩
      · exact absurd e (by rw [e₂]; decide)
      · exact e
  · rw [keepBytes hp (N := 0) (by rdecide) (q₂ i' (by omega)) fr']
    exact h.ek (s₂ e₁).1 i' hi'
  · rw [polyAt_congr (Top.keep hp (by rdecide) q₃ fr')]
    exact (h.t hj).2 (s₂ e₁).1
  · refine (ma (s₂ e₁).2).trans ?_
    rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
    · exact (sv_eq ⟨it, e⟩).symm
    · exact absurd ((s₂ e₁).2) (by rw [e]; decide)

/-- After `Â[i, j] ×_T ŝ[j]` is computed, for `0 < j`. -/
structure S5 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends S4 L i j s₀ s where
  p : Reduced s.mem (Buf.addr s₀ (bP L)) ∧
    (accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bP L)) = multiplyNTTs (aM L s₀ i j) (seP L s₀ j))

/-- Entry `(i, 0)`: `t̂[i] ← Â[i, 0] ×_T ŝ[0]`. -/
theorem entry0_piece (i : Nat) (hi : i < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (R L i 0) (R L i 1) (kgEntry L i 0) := by
  obtain ⟨m₁, -, -, -, -, a₁, -, -⟩ := KgRowOK.mul (L := L)
  have hk : 0 < L.p.k := by omega
  refine sample_piece i 0 hi hk (mulC_piece (Y := Y L) 3 L.kgT 3 L.kgA 3 0 3 L.kgNS KgRowOK.mul0
    (by rdecide) (by yk_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.se 0 (by omega)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  have k := h.toB.keep hp (by rdecide) m₁ (by omega) fr h'
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) a₁ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, h.a (ea ▸ e₁), (h.se 0 (by omega)).2]
  rfl

/-- Entry `(i, j + 1)`: `t̂[i] ← t̂[i] + Â[i, j + 1] ×_T ŝ[j + 1]`. -/
theorem entry_piece (i j : Nat) (hi : i < L.p.k) (hj : j + 1 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (R L i (j + 1)) (R L i (j + 2)) (kgEntry L i (j + 1)) := by
  obtain ⟨-, m₂, m₃, m₄, m₅, -, a₂, o₃⟩ := KgRowOK.mul (L := L)
  have a₃ : (Y L).apart (bACC L) [bT L] = true := by
    have := (KgRowOK.mul (L := L)).2.2.1; simp only [safe, Bool.and_eq_true] at this; exact this.1.1
  refine sample_piece i (j + 1) hi hj (.seq (B := S5 L i (j + 1))
    (mulC_piece (Y := Y L) 3 L.kgP 3 L.kgA 3 (1024 * (j + 1)) 3 L.kgNS (KgRowOK.mulJ (j + 1) hj) (by rdecide)
      (by yk_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.se (j + 1) (by omega)).1⟩)
      fun s₀ s s' hp h h' fr post => ?_) ?_)
  · have k := h.toB.keep hp (by rdecide) m₂ (by omega) fr h'
    have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) a₂ fr
    refine ⟨⟨k, fun hj' => ⟨keepRed hp (by rdecide) m₄ fr (h.t hj').1, fun e₁ => ?_⟩,
      keepRed hp (by rdecide) m₅ fr h.red, fun e₁ => ?_⟩, post.1, fun e₁ => ?_⟩
    · rw [polyAt_congr (Top.keep hp (by rdecide) m₄ fr)]; exact (h.t hj').2 (ea ▸ e₁)
    · rw [polyAt_congr (Top.keep hp (by rdecide) m₅ fr)]; exact h.a (ea ▸ e₁)
    · rw [post.2, h.a (ea ▸ e₁), (h.se (j + 1) (by omega)).2]
  refine accC_piece add_verified add_nosp add_stack 3 L.kgT 3 L.kgP o₃ (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.t (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.toB.keep hp (by rdecide) m₃ (by omega) fr h'
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) a₃ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, (h.t (Nat.succ_pos _)).2 (ea ▸ e₁), h.p.2 (ea ▸ e₁)]
  rfl

/-! ## A row -/

/-- `t̂[i]` is computed. -/
structure S6 (L : KemLay) (i : Nat) (s₀ s : State) : Prop extends B L (L.p.k * i + L.p.k) i s₀ s where
  t : Reduced s.mem (Buf.addr s₀ (bT L)) ∧
    (accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bT L)) = KPke.kgT L.p (aM L s₀) (d s₀) i)

/-- Row `i`: `t̂[i] = Â[i] ∘ ŝ + ê[i]`, encoded into `ek`. -/
theorem row_piece (i : Nat) (hi : i < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (B L (L.p.k * i) i) (B L (L.p.k * (i + 1)) (i + 1)) (kgRow L i) := by
  obtain ⟨o₁, o₂, o₃, o₄, o₅⟩ := KgRowOK.row i hi
  obtain ⟨-, -, m₃, -, -, -, -, -⟩ := KgRowOK.mul (L := L)
  have a₃ : (Y L).apart (bACC L) [bT L] = true := by
    simp only [safe, Bool.and_eq_true] at m₃; exact m₃.1.1
  refine (Piece.seqs0 (P := R L i) L.p.k (fun j hj => match j, hj with
    | 0, _ => entry0_piece i hi
    | j + 1, hj => entry_piece i j hi hj) ?_).mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := S6 L i) (accC_piece add_verified add_nosp add_stack 3 L.kgT 3 (1024 * (L.p.k + i))
    o₁ (by rdecide) (by yk_taint) (fun _ _ _ h => ⟨h.ctx, (h.t (by omega)).1, (h.se (L.p.k + i) (by omega)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.toB.keep hp (by rdecide) m₃ (by omega) fr h'
    have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) a₃ fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, (h.t (by omega)).2 (ea ▸ e₁), (h.se (L.p.k + i) (by omega)).2]
    rfl
  refine enc12C_piece (Y := Y L) 3 L.kgT 1 (384 * i) o₂ (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, h.t.1⟩) fun s₀ s s' hp h h' fr post => ?_
  obtain ⟨k₁, k₂⟩ := keepS hp (by rdecide) o₃ fr h.rho h.se
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) o₄ fr
  refine ⟨h', k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i' hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
  · rw [keepBytes hp (by rdecide) (o₅ i' hi') fr]; exact h.ek (ea ▸ e₁) i' hi'
  · rw [post, h.t.2 (ea ▸ e₁)]

/-- The `k` rows, then `c`. -/
theorem rows_piece {Q : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (B L (L.p.k * L.p.k) L.p.k) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (B L 0 0) Q (seqs ((List.range L.p.k).map (kgRow L)) c) :=
  Piece.seqs0 (P := fun i => B L (L.p.k * i) i) L.p.k row_piece h

end VG.Proof.MlKem.X86.KeyGen
