import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Spec.MlKem.Contract
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Spec.MlKem

section

section

/-!
# ML-KEM: the hash functions and XOFs through the streaming sponge

Untrusted: everything here is checked by Lean. What a caller of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze`
(`Spec/Sha3/Contract.lean`) needs to conclude that it computed `H`, `J`,
`G`, `PRF` or `XOF` (§4.1): from the all-zero state, which represents the
empty message (`repr_nil`), absorbing the pieces of the message, padding
with the suffix of the function (`sha3Suffix32`, `shakeSuffix32`), and
squeezing from position 0 gives the function (`H_eq`, `J_eq`, `G_eq`,
`prf_eq`, `xof_eq`, as `squeezeFrom` of the padded state `padded`); and
output squeezed in pieces is the concatenation (`squeezeFrom_append`).
Byte `p` of the XOF output is the same whatever the length asked for
(`xof_getD`, `xofByte`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem
open VG.Spec.Sha3
open VG.Proof.Sha3 (Rep rep_nil byteOf iterF length_squeezeFrom squeezeFrom_getElem length_squeeze
  squeeze_getElem)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`:
what `vg_keccak_pad` leaves (`padContract`). -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : State := absorb rate (pad rate suffix m)

/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Repr mem p rate [] := by
  show stateAt mem p = Rep rate []
  rw [rep_nil, h]

/-- The `suffix` argument of `vg_keccak_pad` for SHA-3. -/
theorem sha3Suffix32 : (0x06 : BitVec 32).setWidth 8 = sha3Suffix := by decide

/-- The `suffix` argument of `vg_keccak_pad` for SHAKE. -/
theorem shakeSuffix32 : (0x1f : BitVec 32).setWidth 8 = shakeSuffix := by decide

theorem rate72 : 72 ∈ rates := by decide
theorem rate136 : 136 ∈ rates := by decide
theorem rate168 : 168 ∈ rates := by decide

/-- Output from position 0 is the output of `squeeze`. -/
theorem squeezeFrom_zero (rate : Nat) (S : State) (d : Nat) : squeezeFrom rate S 0 d = squeeze rate S d := by
  simp only [squeezeFrom, squeeze, Nat.zero_add, List.drop_zero]

/-- Output squeezed in two pieces. -/
theorem squeezeFrom_append {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) (p a b : Nat) :
    squeezeFrom rate S p a ++ squeezeFrom rate S (p + a) b = squeezeFrom rate S p (a + b) := by
  refine List.ext_getElem (by rw [List.length_append, length_squeezeFrom hr hr', length_squeezeFrom hr hr',
    length_squeezeFrom hr hr']) fun i h₁ h₂ => ?_
  rw [length_squeezeFrom hr hr'] at h₂
  rw [squeezeFrom_getElem hr hr' _ h₂, List.getElem_append]
  split
  · rename_i h
    rw [length_squeezeFrom hr hr'] at h
    rw [squeezeFrom_getElem hr hr' _ h]
  · rename_i h
    rw [length_squeezeFrom hr hr'] at h
    rw [squeezeFrom_getElem hr hr' _ (by rw [length_squeezeFrom hr hr']; omega),
      show p + a + (i - (squeezeFrom rate S p a).length) = p + i by
        rw [length_squeezeFrom hr hr']; omega]

/-- The first `d` bytes of a longer output. -/
theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d := by
  refine List.ext_getElem (by simp [length_squeeze hr hr']; omega) fun i h₁ h₂ => ?_
  rw [length_squeeze hr hr'] at h₂
  rw [List.getElem_take, squeeze_getElem hr hr' _ h₂, squeeze_getElem hr hr' _ (by omega)]

/-! ## The functions of §4.1 -/

theorem sha3_256_eq (m : List Byte) : sha3_256 m = squeezeFrom 136 (padded 136 sha3Suffix m) 0 32 := by
  rw [squeezeFrom_zero]; rfl

theorem sha3_512_eq (m : List Byte) : sha3_512 m = squeezeFrom 72 (padded 72 sha3Suffix m) 0 64 := by
  rw [squeezeFrom_zero]; rfl

theorem shake128_eq (m : List Byte) (d : Nat) :
    shake128 m d = squeezeFrom 168 (padded 168 shakeSuffix m) 0 d := by
  rw [squeezeFrom_zero]; rfl

theorem shake256_eq (m : List Byte) (d : Nat) :
    shake256 m d = squeezeFrom 136 (padded 136 shakeSuffix m) 0 d := by
  rw [squeezeFrom_zero]; rfl

/-- `H(s) = SHA3-256(s)`: rate 136, suffix `0x06`, 32 bytes. -/
theorem H_eq (s : List Byte) : H s = squeezeFrom 136 (padded 136 sha3Suffix s) 0 32 := sha3_256_eq s

/-- `J(s) = SHAKE256(s, 256)`: rate 136, suffix `0x1f`, 32 bytes. -/
theorem J_eq (s : List Byte) : J s = squeezeFrom 136 (padded 136 shakeSuffix s) 0 32 := shake256_eq s 32

/-- `G(c) = SHA3-512(c)`, as its halves: rate 72, suffix `0x06`, 32 bytes
from position 0 and 32 bytes from position 32. -/
theorem G_eq (c : List Byte) :
    G c = (squeezeFrom 72 (padded 72 sha3Suffix c) 0 32, squeezeFrom 72 (padded 72 sha3Suffix c) 32 32) := by
  have e := squeezeFrom_append (rate := 72) (by decide) (by decide) (padded 72 sha3Suffix c) 0 32 32
  have hl := length_squeezeFrom (rate := 72) (by decide) (by decide) (padded 72 sha3Suffix c) 0 32
  simp only [G, sha3_512_eq, ← e, List.take_left' hl, List.drop_left' hl]

/-- `PRF_η(s, b) = SHAKE256(s ‖ b, 8 · 64η)`: rate 136, suffix `0x1f`,
`64η` bytes. -/
theorem prf_eq (η : Nat) (s : List Byte) (b : Byte) :
    prf η s b = squeezeFrom 136 (padded 136 shakeSuffix (s ++ [b])) 0 (64 * η) := shake256_eq _ _

/-- `XOF` (SHAKE128): rate 168, suffix `0x1f`. -/
theorem xof_eq (B : List Byte) (ℓ : Nat) : xof B ℓ = squeezeFrom 168 (padded 168 shakeSuffix B) 0 ℓ :=
  shake128_eq B ℓ

theorem H_length (s : List Byte) : (H s).length = 32 := length_squeeze (by decide) (by decide) _ _

theorem J_length (s : List Byte) : (J s).length = 32 := length_squeeze (by decide) (by decide) _ _

theorem G_fst_length (c : List Byte) : (G c).1.length = 32 := by
  simp only [G, List.length_take]
  rw [show (sha3_512 c).length = 64 from length_squeeze (by decide) (by decide) _ _]
  rfl

theorem G_snd_length (c : List Byte) : (G c).2.length = 32 := by
  simp only [G, List.length_drop]
  rw [show (sha3_512 c).length = 64 from length_squeeze (by decide) (by decide) _ _]

theorem prf_length (η : Nat) (s : List Byte) (b : Byte) : (prf η s b).length = 64 * η :=
  length_squeeze (by decide) (by decide) _ _

/-- Byte `p` of the output of `XOF` after absorbing `B`: byte `p mod 168`
of the padded state after `⌊p / 168⌋` more permutations. -/
def xofByte (B : List Byte) (p : Nat) : Byte :=
  byteOf (iterF (p / 168) (padded 168 shakeSuffix B)) (p % 168)

theorem xof_length (B : List Byte) (ℓ : Nat) : (xof B ℓ).length = ℓ :=
  length_squeeze (by decide) (by decide) _ _

theorem xof_getD (B : List Byte) {ℓ p : Nat} (hp : p < ℓ) : (xof B ℓ).getD p 0 = xofByte B p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [xof_length]; exact hp),
    Option.getD_some]
  exact squeeze_getElem (by decide) (by decide) _ hp

/-- Byte `i` of output squeezed from position `pos` of the XOF. -/
theorem xof_squeezeFrom_getElem (B : List Byte) {pos d i : Nat} (hi : i < d) :
    (squeezeFrom 168 (padded 168 shakeSuffix B) pos d)[i]'(by
      rw [length_squeezeFrom (by decide) (by decide)]; exact hi) = xofByte B (pos + i) :=
  squeezeFrom_getElem (by decide) (by decide) _ hi

end VG.Proof.MlKem

end

/-!
# ML-KEM: SampleNTT as a loop, and bounds on its iterations

Untrusted: everything here is checked by Lean. `SampleNTT` (Algorithm 7) as
the loop an implementation runs over the 3-byte chunks of the XOF output
(`xofByte`, above): `sampleAfter a out t` is the list of coefficients
accepted after the first `t` chunks, which stops growing once it has 256
(`sampleStepCap`). An implementation that bounds the loop by `iters`
iterations and stops after `t ≤ iters` chunks with 256 coefficients
computes `sampleNTT iters B` (`sampleNTT_of_full`); one that reaches the
bound with fewer has `sampleNTT iters B = none` (`sampleNTT_none`).

A bigger bound gives the same result once the result is `some`
(`sampleNTT_mono`), and so do the algorithms built on `SampleNTT`
(`kpkeKeyGen_mono`, `kpkeEncrypt_mono`, `keyGenInternal_mono`,
`encapsInternal_mono`, `decapsInternal_mono`), and `Outcome` holds for an
implementation that bounds each `SampleNTT` by `minIterations`
(`outcome_of_min`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## One iteration -/

/-- Lines 5–15 of Algorithm 7 on the chunk `C = (c₀, c₁, c₂)`, from the
coefficients `a` sampled so far. -/
def sampleStep (a : List Zq) (c₀ c₁ c₂ : Byte) : List Zq :=
  let d₁ := c₀.toNat + 256 * (c₁.toNat % 16)
  let d₂ := c₁.toNat / 16 + 16 * c₂.toNat
  let a := if d₁ < q then a ++ [ofNat d₁] else a
  if d₂ < q ∧ a.length < n then a ++ [ofNat d₂] else a

/-- An iteration of the loop, which does nothing once there are 256
coefficients (the loop has ended). -/
def sampleStepCap (a : List Zq) (c₀ c₁ c₂ : Byte) : List Zq :=
  if a.length = n then a else sampleStep a c₀ c₁ c₂

/-- The coefficients sampled from `a` on after the first `t` chunks of the
bytes `out`, the loop stopping at 256 coefficients. -/
def sampleAfter (a : List Zq) (out : Nat → Byte) : Nat → List Zq
  | 0 => a
  | t + 1 => sampleStepCap (sampleAfter a out t) (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2))

/-- The element of `T_q` whose coefficients are the first 256 of `a`. -/
def toPoly (a : List Zq) : Poly := Vector.ofFn fun i => a.getD i.val 0

theorem sampleAfter_zero (a : List Zq) (out : Nat → Byte) : sampleAfter a out 0 = a := rfl

theorem sampleAfter_succ (a : List Zq) (out : Nat → Byte) (t : Nat) :
    sampleAfter a out (t + 1) =
      sampleStepCap (sampleAfter a out t) (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2)) := rfl

theorem sampleStep_length (a : List Zq) (c₀ c₁ c₂ : Byte) (ha : a.length < n) :
    (sampleStep a c₀ c₁ c₂).length ≤ n := by
  simp only [sampleStep]
  split <;> split <;> simp_all <;> omega

theorem sampleStepCap_length {a : List Zq} (ha : a.length ≤ n) (c₀ c₁ c₂ : Byte) :
    (sampleStepCap a c₀ c₁ c₂).length ≤ n := by
  unfold sampleStepCap
  split
  · exact ha
  · exact sampleStep_length a c₀ c₁ c₂ (by omega)

theorem sampleStepCap_full {a : List Zq} (ha : a.length = n) (c₀ c₁ c₂ : Byte) :
    sampleStepCap a c₀ c₁ c₂ = a := by
  unfold sampleStepCap; rw [ite_eq_left ha]

/-- An iteration keeps the coefficients sampled before it. -/
theorem sampleStepCap_prefix (a : List Zq) (c₀ c₁ c₂ : Byte) : a <+: sampleStepCap a c₀ c₁ c₂ := by
  unfold sampleStepCap sampleStep
  split
  · exact List.prefix_refl a
  · dsimp only
    split <;> split
    all_goals first
      | exact List.prefix_refl a
      | exact List.prefix_append a _
      | exact (List.prefix_append a _).trans (List.prefix_append _ _)

theorem sampleAfter_length_le {a : List Zq} (ha : a.length ≤ n) (out : Nat → Byte) :
    ∀ t, (sampleAfter a out t).length ≤ n
  | 0 => ha
  | t + 1 => sampleStepCap_length (sampleAfter_length_le ha out t) _ _ _

/-- Once there are 256 coefficients, they stay. -/
theorem sampleAfter_full {a : List Zq} {out : Nat → Byte} {t : Nat} (h : (sampleAfter a out t).length = n) :
    ∀ t', t ≤ t' → sampleAfter a out t' = sampleAfter a out t := by
  intro t' ht
  have : ∀ k, sampleAfter a out (t + k) = sampleAfter a out t := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← Nat.add_assoc, sampleAfter_succ, ih, sampleStepCap_full h]
  rw [← this (t' - t), Nat.add_sub_cancel' ht]

/-- The coefficients sampled only depend on the bytes of the chunks read. -/
theorem sampleAfter_congr (a : List Zq) {out out' : Nat → Byte} :
    ∀ {t}, (∀ p < 3 * t, out p = out' p) → sampleAfter a out t = sampleAfter a out' t
  | 0, _ => rfl
  | t + 1, h => by
    rw [sampleAfter_succ, sampleAfter_succ, sampleAfter_congr a fun p hp => h p (by omega),
      h _ (by omega), h _ (by omega), h _ (by omega)]

/-- The first chunk, then the others. -/
theorem sampleAfter_succ' (a : List Zq) (out : Nat → Byte) :
    ∀ t, sampleAfter a out (t + 1) =
      sampleAfter (sampleStepCap a (out 0) (out 1) (out 2)) (fun p => out (p + 3)) t
  | 0 => rfl
  | t + 1 => by
    rw [sampleAfter_succ, sampleAfter_succ' a out t, sampleAfter_succ]
    congr 2 <;> congr 1 <;> omega

/-! ## The loop of the standard -/

/-- `sampleLoop` after it stops: the coefficients if there are 256. -/
private theorem sampleLoop_eq_after :
    ∀ (L : List Byte) (a : List Zq), a.length ≤ n →
      sampleLoop a L =
        if (sampleAfter a (fun p => L.getD p 0) (L.length / 3)).length = n
        then some (sampleAfter a (fun p => L.getD p 0) (L.length / 3)) else none
  | c₀ :: c₁ :: c₂ :: L, a, ha => by
    rw [sampleLoop]
    by_cases h : a.length = n
    · rw [ite_eq_left h, sampleAfter_full (t := 0) h _ (Nat.zero_le _), sampleAfter_zero, ite_eq_left h]
    · rw [ite_eq_right h]
      have hs : (c₀ :: c₁ :: c₂ :: L).length / 3 = L.length / 3 + 1 := by simp; omega
      have hf : (fun p => (c₀ :: c₁ :: c₂ :: L).getD (p + 3) 0) = fun p => L.getD p 0 := by
        funext p; simp only [List.getD_cons_succ]
      rw [hs, sampleAfter_succ', hf]
      simp only [List.getD_cons_zero, List.getD_cons_succ, sampleStepCap, ite_eq_right h]
      exact sampleLoop_eq_after L _ (sampleStep_length a c₀ c₁ c₂ (by omega))
  | [], a, _ => by
    rw [show ([] : List Byte).length / 3 = 0 by simp, sampleAfter_zero]; unfold sampleLoop; rfl
  | [x], a, _ => by
    rw [show [x].length / 3 = 0 by simp, sampleAfter_zero]; unfold sampleLoop; rfl
  | [x, y], a, _ => by
    rw [show [x, y].length / 3 = 0 by simp, sampleAfter_zero]; unfold sampleLoop; rfl

/-- `SampleNTT` with its loop bounded by `iters` iterations, as the
coefficients sampled after `iters` chunks of the XOF output. -/
theorem sampleNTT_eq (iters : Nat) (B : List Byte) :
    sampleNTT iters B =
      if (sampleAfter [] (xofByte B) iters).length = n
      then some (toPoly (sampleAfter [] (xofByte B) iters)) else none := by
  rw [sampleNTT, sampleLoop_eq_after _ [] (Nat.zero_le _), xof_length,
    show 3 * iters / 3 = iters by omega,
    sampleAfter_congr [] (out' := xofByte B) fun p hp => xof_getD B hp]
  split <;> rfl

/-- An implementation that has 256 coefficients after `t ≤ iters` chunks
computes `SampleNTT` bounded by `iters`. -/
theorem sampleNTT_of_full {iters t : Nat} {B : List Byte} (ht : t ≤ iters)
    (h : (sampleAfter [] (xofByte B) t).length = n) :
    sampleNTT iters B = some (toPoly (sampleAfter [] (xofByte B) t)) := by
  rw [sampleNTT_eq, sampleAfter_full h _ ht, ite_eq_left h]

/-- An implementation that has fewer than 256 coefficients after `iters`
chunks: `SampleNTT` bounded by `iters` fails. -/
theorem sampleNTT_none {iters : Nat} {B : List Byte} (h : (sampleAfter [] (xofByte B) iters).length ≠ n) :
    sampleNTT iters B = none := by
  rw [sampleNTT_eq, ite_eq_right h]

/-- A bigger bound on the iterations gives the same result. -/
theorem sampleNTT_mono {iters iters' : Nat} {B : List Byte} {a : Poly} (h : sampleNTT iters B = some a)
    (hi : iters ≤ iters') : sampleNTT iters' B = some a := by
  rw [sampleNTT_eq] at h
  split at h
  · rename_i hf
    rw [sampleNTT_of_full hi hf, h]
  · cases h

/-! ## The algorithms that sample -/

/-- `f` with a bound on the iterations of `SampleNTT` gives the same result
with any bigger bound, once it is `some`. -/
def Mono {α : Type} (f : Nat → Option α) : Prop :=
  ∀ ⦃iters iters' : Nat⦄ ⦃a : α⦄, f iters = some a → iters ≤ iters' → f iters' = some a

theorem Mono.bind {α β : Type} {f : Nat → Option α} (hf : Mono f) (g : α → Option β) :
    Mono fun iters => (f iters).bind g := by
  intro i i' b h hi
  dsimp only at h ⊢
  cases hx : f i with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; rw [hf hx hi]; exact h

theorem Mono.map {α β : Type} {f : Nat → Option α} (hf : Mono f) (g : α → β) :
    Mono fun iters => (f iters).map g := by
  intro i i' b h hi
  dsimp only at h ⊢
  cases hx : f i with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; rw [hf hx hi]; exact h

theorem mapM_mono {α β : Type} {f : α → Nat → Option β} (hf : ∀ x, Mono (f x)) :
    ∀ L : List α, Mono fun iters => L.mapM fun x => f x iters
  | [] => fun _ _ _ h _ => h
  | x :: L => by
    intro i i' b h hi
    simp only [List.mapM_cons] at h ⊢
    cases hx : f x i with
    | none => rw [hx] at h; cases h
    | some y =>
      rw [hx] at h
      cases hL : L.mapM (fun x => f x i) with
      | none => rw [hL] at h; cases h
      | some ys =>
        rw [hL] at h
        simp only [hf x hx hi, mapM_mono hf L hL hi]
        exact h

theorem sampleNTT_mono' (B : List Byte) : Mono fun iters => sampleNTT iters B :=
  fun _ _ _ h hi => sampleNTT_mono h hi

theorem sampleMatrix_mono (k : Nat) (ρ : List Byte) : Mono fun iters => sampleMatrix k iters ρ :=
  mapM_mono (fun _ => mapM_mono (fun _ => sampleNTT_mono' _) _) _

theorem kpkeKeyGen_mono (p : Params) (d : List Byte) : Mono fun iters => kpkeKeyGen p iters d := by
  simp only [kpkeKeyGen]
  exact (sampleMatrix_mono _ _).bind _

theorem kpkeEncrypt_mono (p : Params) (ek m r : List Byte) :
    Mono fun iters => kpkeEncrypt p iters ek m r := by
  simp only [kpkeEncrypt]
  exact (sampleMatrix_mono _ _).bind _

theorem keyGenInternal_mono (p : Params) (d z : List Byte) :
    Mono fun iters => keyGenInternal p iters d z := by
  simp only [keyGenInternal]
  exact (kpkeKeyGen_mono p d).bind _

theorem encapsInternal_mono (p : Params) (ek m : List Byte) :
    Mono fun iters => encapsInternal p iters ek m := by
  simp only [encapsInternal]
  exact (kpkeEncrypt_mono p ek m _).bind _

theorem decapsInternal_mono (p : Params) (dk c : List Byte) :
    Mono fun iters => decapsInternal p iters dk c := by
  simp only [decapsInternal]
  exact (kpkeEncrypt_mono p _ _ _).bind _

/-- The return value of an implementation that bounds each `SampleNTT` by
`minIterations` iterations: 1 if the algorithm so bounded succeeds, and 0
if not. -/
theorem outcome_of_min {α : Type} {f : Nat → Option α} {r : BitVec 32} {out : α}
    (h : (r = 1 ∧ f minIterations = some out) ∨ (r = 0 ∧ f minIterations = none)) :
    Outcome f r out := by
  rcases h with ⟨hr, hf⟩ | ⟨hr, hf⟩
  · exact .inl ⟨hr, minIterations, hf⟩
  · exact .inr ⟨hr, hf⟩

end VG.Proof.MlKem

end

/-!
# ML-KEM-768: K-PKE and the internal algorithms as polynomial steps

Untrusted: everything here is checked by Lean. K-PKE.KeyGen, K-PKE.Encrypt,
K-PKE.Decrypt (Algorithms 13–15) and the internal algorithms of ML-KEM-768
(Algorithms 16–18) restated, for `k = 3`, as the sequence of calls of the
polynomial primitives (`Spec/MlKem/Poly.lean`) an implementation makes, so
that a proof of the top-level functions chains the primitives' contracts:

* `dot3 a b = (a₀ ×_T b₀ + a₁ ×_T b₁) + a₂ ×_T b₂`, accumulated left to right
  with `add` (`dot_eq_dot3`);
* the matrix `Â` from the nine `SampleNTT`s (`sampleMatrix_some`,
  `sampleMatrix_none`);
* K-PKE.KeyGen: `t̂[i] = dot3 (Â[i]) ŝ + ê[i]`, `ek = ByteEncode₁₂(t̂[0]) ‖ … ‖ ρ`,
  `dk = ByteEncode₁₂(ŝ[0]) ‖ …` (`kpkeKeyGen768_some`, `kpkeKeyGen768_none`);
* K-PKE.Encrypt: `u[i] = NTT⁻¹(dot3 (Â[·][i]) ŷ) + e₁[i]`,
  `v = NTT⁻¹(dot3 t̂ ŷ) + e₂ + μ`, the ciphertext the compressed encodings of
  `u[0]`, `u[1]`, `u[2]` and `v` (`kpkeEncrypt768_some`, `kpkeEncrypt768_none`);
* K-PKE.Decrypt (`kpkeDecrypt768`);
* the internal algorithms, and the layout of the decapsulation key
  (`keyGenInternal768`, `encapsInternal768`, `decapsInternal768`): decapsulation
  selects between `K'` and `K̄` by whether `c = c'`, which
  `eq_iff_foldl_or_xor` computes without branching.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## Sums of products -/

/-- `∑_{j<3} a j ×_{T_q} b j`, accumulated left to right with `add`. -/
def dot3 (a b : Nat → Poly) : Poly :=
  add (add (multiplyNTTs (a 0) (b 0)) (multiplyNTTs (a 1) (b 1))) (multiplyNTTs (a 2) (b 2))

theorem list_range3 {α : Type} (a : Nat → α) : (List.range 3).map a = [a 0, a 1, a 2] := rfl

theorem dot_eq_dot3 (a b : Nat → Poly) : dot [a 0, a 1, a 2] [b 0, b 1, b 2] = dot3 a b := by
  simp only [dot, List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil,
    zero_add_poly, dot3]

/-! ## The matrix -/

theorem mapM_range_some {β : Type} {f : Nat → Option β} {a : Nat → β} :
    ∀ {k : Nat} (s : Nat), (∀ i < k, f (s + i) = some (a (s + i))) →
      (List.range' s k).mapM f = some ((List.range' s k).map a)
  | 0, _, _ => rfl
  | k + 1, s, h => by
    rw [List.range'_succ, List.mapM_cons, List.map_cons]
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [h0, mapM_range_some (k := k) (s + 1) fun i hi => by
      rw [show s + 1 + i = s + (i + 1) by omega]; exact h (i + 1) (by omega)]
    rfl

theorem mapM_none {α β : Type} {f : α → Option β} : ∀ {L : List α} {x : α}, x ∈ L → f x = none →
    L.mapM f = none
  | y :: L, x, hx, h => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [h]; rfl
    · cases hy : f y with
      | none => rfl
      | some b => rw [mapM_none hx h]; rfl

/-- The seed `ρ ‖ j ‖ i` of `Â[i, j]`. -/
def matSeed (ρ : List Byte) (i j : Nat) : List Byte := ρ ++ [BitVec.ofNat 8 j, BitVec.ofNat 8 i]

/-- The `k × k` matrix with entries `a i j`, as its rows. -/
def matrix (k : Nat) (a : Nat → Nat → Poly) : List (List Poly) :=
  (List.range k).map fun i => (List.range k).map fun j => a i j

theorem sampleMatrix_some {k iters : Nat} {ρ : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < k, ∀ j < k, sampleNTT iters (matSeed ρ i j) = some (a i j)) :
    sampleMatrix k iters ρ = some (matrix k a) := by
  rw [sampleMatrix, matrix, List.range_eq_range']
  refine mapM_range_some 0 fun i hi => ?_
  rw [Nat.zero_add]
  exact mapM_range_some 0 fun j hj => by rw [Nat.zero_add]; exact h i hi j hj

theorem sampleMatrix_none {k iters : Nat} {ρ : List Byte} {i j : Nat} (hi : i < k) (hj : j < k)
    (h : sampleNTT iters (matSeed ρ i j) = none) : sampleMatrix k iters ρ = none :=
  mapM_none (List.mem_range.mpr hi) (by
    cases hm : (List.range k).mapM (fun j => sampleNTT iters (ρ ++ [BitVec.ofNat 8 j, BitVec.ofNat 8 i]))
    · rfl
    · rw [mapM_none (List.mem_range.mpr hj) h] at hm; cases hm)

/-! ## K-PKE.KeyGen -/

/-- `SamplePolyCBD₂(PRF₂(s, N))`. -/
def cbd (s : List Byte) (N : Nat) : Poly := samplePolyCBD 2 (prf 2 s (BitVec.ofNat 8 N))

/-- `ρ` of K-PKE.KeyGen(d): the first half of `G(d ‖ 3)`. -/
def kgRho (d : List Byte) : List Byte := (G (d ++ [BitVec.ofNat 8 3])).1

/-- `σ` of K-PKE.KeyGen(d): the second half of `G(d ‖ 3)`. -/
def kgSigma (d : List Byte) : List Byte := (G (d ++ [BitVec.ofNat 8 3])).2

/-- `ŝ[j] = NTT(SamplePolyCBD₂(PRF₂(σ, j)))`. -/
def kgS (d : List Byte) (j : Nat) : Poly := ntt (cbd (kgSigma d) j)

/-- `ê[i] = NTT(SamplePolyCBD₂(PRF₂(σ, 3 + i)))`. -/
def kgE (d : List Byte) (i : Nat) : Poly := ntt (cbd (kgSigma d) (3 + i))

/-- `t̂[i] = Â[i] ∘ ŝ + ê[i]`. -/
def kgT (a : Nat → Nat → Poly) (d : List Byte) (i : Nat) : Poly := add (dot3 (a i) (kgS d)) (kgE d i)

/-- `ek_PKE = ByteEncode₁₂(t̂[0]) ‖ ByteEncode₁₂(t̂[1]) ‖ ByteEncode₁₂(t̂[2]) ‖ ρ`. -/
def ekPKE768 (a : Nat → Nat → Poly) (d : List Byte) : List Byte :=
  encode12 (kgT a d 0) ++ encode12 (kgT a d 1) ++ encode12 (kgT a d 2) ++ kgRho d

/-- `dk_PKE = ByteEncode₁₂(ŝ[0]) ‖ ByteEncode₁₂(ŝ[1]) ‖ ByteEncode₁₂(ŝ[2])`. -/
def dkPKE768 (d : List Byte) : List Byte :=
  encode12 (kgS d 0) ++ encode12 (kgS d 1) ++ encode12 (kgS d 2)

theorem kgRho_eq (d : List Byte) : keyGenRho mlKem768 d = kgRho d := rfl

private theorem kpkeKeyGen768_eq (iters : Nat) (d : List Byte) :
    kpkeKeyGen mlKem768 iters d =
      (sampleMatrix 3 iters (kgRho d)).bind fun A =>
        some (encodeVec (addVec (mulMatVec A ((List.range 3).map (kgS d)))
          ((List.range 3).map (kgE d))) ++ kgRho d, encodeVec ((List.range 3).map (kgS d))) := by
  rfl

theorem kpkeKeyGen768_some {iters : Nat} {d : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 3, ∀ j < 3, sampleNTT iters (matSeed (kgRho d) i j) = some (a i j)) :
    kpkeKeyGen mlKem768 iters d = some (ekPKE768 a d, dkPKE768 d) := by
  rw [kpkeKeyGen768_eq, sampleMatrix_some h, Option.bind_some]
  simp only [matrix, list_range3, mulMatVec, List.map_cons, List.map_nil, addVec, List.zipWith_cons_cons,
    List.zipWith_nil_left, encodeVec, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc, ekPKE768, dkPKE768, kgT]
  rw [dot_eq_dot3, dot_eq_dot3, dot_eq_dot3]

theorem kpkeKeyGen768_none {iters : Nat} {d : List Byte} {i j : Nat} (hi : i < 3) (hj : j < 3)
    (h : sampleNTT iters (matSeed (kgRho d) i j) = none) : kpkeKeyGen mlKem768 iters d = none := by
  rw [kpkeKeyGen768_eq, sampleMatrix_none hi hj h]; rfl

theorem ekPKE768_length (a : Nat → Nat → Poly) (d : List Byte) : (ekPKE768 a d).length = 1184 := by
  simp only [ekPKE768, List.length_append, encode12_length, kgRho, G_fst_length]

theorem dkPKE768_length (d : List Byte) : (dkPKE768 d).length = 1152 := by
  simp only [dkPKE768, List.length_append, encode12_length]

/-! ## K-PKE.Encrypt -/

/-- `((L.take N).drop s).take c = (L.drop s).take c` when `s + c ≤ N`. -/
theorem slice_take {α : Type} (L : List α) {N s c : Nat} (h : s + c ≤ N) :
    ((L.take N).drop s).take c = (L.drop s).take c := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])`. -/
def ekT (ek : List Byte) (i : Nat) : Poly := decode12 ((ek.drop (384 * i)).take 384)

/-- `ŷ[j] = NTT(SamplePolyCBD₂(PRF₂(r, j)))`. -/
def encY (r : List Byte) (j : Nat) : Poly := ntt (cbd r j)

/-- `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, with `e₁[i] = SamplePolyCBD₂(PRF₂(r, 3 + i))`. -/
def encU (a : Nat → Nat → Poly) (r : List Byte) (i : Nat) : Poly :=
  add (nttInv (dot3 (fun j => a j i) (encY r))) (cbd r (3 + i))

/-- `v = NTT⁻¹(t̂ ∘ ŷ) + e₂ + μ`, with `e₂ = SamplePolyCBD₂(PRF₂(r, 6))` and
`μ = Decompress₁(ByteDecode₁(m))`. -/
def encV (ek m r : List Byte) : Poly :=
  add (add (nttInv (dot3 (ekT ek) (encY r))) (cbd r 6)) (decodeDecompress 1 m)

/-- The ciphertext: `ByteEncode₁₀(Compress₁₀(u[i]))` for `i < 3`, then
`ByteEncode₄(Compress₄(v))`. -/
def ct768 (a : Nat → Nat → Poly) (ek m r : List Byte) : List Byte :=
  compressEncode 10 (encU a r 0) ++ compressEncode 10 (encU a r 1) ++ compressEncode 10 (encU a r 2) ++
    compressEncode 4 (encV ek m r)

theorem ct768_length (a : Nat → Nat → Poly) (ek m r : List Byte) : (ct768 a ek m r).length = 1088 := by
  simp only [ct768, List.length_append, compressEncode_length]

private theorem kpkeEncrypt768_eq (iters : Nat) (ek m r : List Byte) :
    kpkeEncrypt mlKem768 iters ek m r =
      (sampleMatrix 3 iters (ekRho mlKem768 ek)).bind fun A =>
        some ((addVec ((mulMatTVec 3 A ((List.range 3).map (encY r))).map nttInv)
            ((List.range 3).map fun i => cbd r (3 + i))).flatMap (compressEncode 10) ++
          compressEncode 4 (add (add (nttInv (dot (decodeVec 3 (ek.take 1152))
            ((List.range 3).map (encY r)))) (cbd r 6)) (decodeDecompress 1 m))) := by
  rfl

theorem decodeVec768 (ek : List Byte) : decodeVec 3 (ek.take 1152) = [ekT ek 0, ekT ek 1, ekT ek 2] := by
  simp only [decodeVec, list_range3, ekT, slice_take ek (show 384 * 0 + 384 ≤ 1152 by decide),
    slice_take ek (show 384 * 1 + 384 ≤ 1152 by decide), slice_take ek (show 384 * 2 + 384 ≤ 1152 by decide)]

theorem kpkeEncrypt768_some {iters : Nat} {ek m r : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 3, ∀ j < 3, sampleNTT iters (matSeed (ekRho mlKem768 ek) i j) = some (a i j)) :
    kpkeEncrypt mlKem768 iters ek m r = some (ct768 a ek m r) := by
  rw [kpkeEncrypt768_eq, sampleMatrix_some h, Option.bind_some, decodeVec768]
  simp only [matrix, list_range3, mulMatTVec, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, addVec, List.zipWith_cons_cons, List.zipWith_nil_left, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc, ct768, encU, encV, ← dot_eq_dot3]

theorem kpkeEncrypt768_none {iters : Nat} {ek m r : List Byte} {i j : Nat} (hi : i < 3) (hj : j < 3)
    (h : sampleNTT iters (matSeed (ekRho mlKem768 ek) i j) = none) :
    kpkeEncrypt mlKem768 iters ek m r = none := by
  rw [kpkeEncrypt768_eq, sampleMatrix_none hi hj h]; rfl

/-! ## K-PKE.Decrypt -/

/-- `u'[i] = Decompress₁₀(ByteDecode₁₀(c[320i : 320i + 320]))`. -/
def dcU (c : List Byte) (i : Nat) : Poly := decodeDecompress 10 ((c.drop (320 * i)).take 320)

/-- `v' = Decompress₄(ByteDecode₄(c[960 : 1088]))`. -/
def dcV (c : List Byte) : Poly := decodeDecompress 4 ((c.drop 960).take 128)

/-- `ŝ[i] = ByteDecode₁₂(dk[384i : 384i + 384])`. -/
def dcS (dk : List Byte) (i : Nat) : Poly := decode12 ((dk.drop (384 * i)).take 384)

/-- K-PKE.Decrypt of ML-KEM-768: `w = v' - NTT⁻¹(ŝ ∘ NTT(u'))`, and
`m = ByteEncode₁(Compress₁(w))`. -/
theorem kpkeDecrypt768 (dk c : List Byte) :
    kpkeDecrypt mlKem768 dk c =
      compressEncode 1 (sub (dcV c) (nttInv (dot3 (dcS dk) fun i => ntt (dcU c i)))) := by
  have e : kpkeDecrypt mlKem768 dk c = compressEncode 1 (sub (decodeDecompress 4 ((c.drop 960).take 128))
      (nttInv (dot (decodeVec 3 dk) (((List.range 3).map fun i =>
        decodeDecompress 10 (((c.take 960).drop (320 * i)).take 320)).map ntt)))) := rfl
  rw [e, ← dot_eq_dot3]
  simp only [decodeVec, list_range3, List.map_cons, List.map_nil, dcV, dcS, dcU,
    slice_take c (show 320 * 0 + 320 ≤ 960 by decide), slice_take c (show 320 * 1 + 320 ≤ 960 by decide),
    slice_take c (show 320 * 2 + 320 ≤ 960 by decide)]

/-! ## The internal algorithms -/

/-- `ML-KEM.KeyGen_internal(d, z)` of ML-KEM-768: `dk = dk_PKE ‖ ek ‖ H(ek) ‖ z`. -/
theorem keyGenInternal768 (iters : Nat) (d z : List Byte) :
    keyGenInternal mlKem768 iters d z =
      (kpkeKeyGen mlKem768 iters d).map fun k => (k.1, k.2 ++ k.1 ++ H k.1 ++ z) := by
  simp only [keyGenInternal]
  cases kpkeKeyGen mlKem768 iters d <;> rfl

/-- `ML-KEM.Encaps_internal(ek, m)` of ML-KEM-768: `(K, r) = G(m ‖ H(ek))`,
and the ciphertext of K-PKE.Encrypt with `r`. -/
theorem encapsInternal768 (iters : Nat) (ek m : List Byte) :
    encapsInternal mlKem768 iters ek m =
      (kpkeEncrypt mlKem768 iters ek m (G (m ++ H ek)).2).map fun c => ((G (m ++ H ek)).1, c) := by
  simp only [encapsInternal]
  cases kpkeEncrypt mlKem768 iters ek m (G (m ++ H ek)).2 <;> rfl

/-- `dk_PKE = dk[0 : 1152]`. -/
def dkPke (dk : List Byte) : List Byte := dk.take 1152

/-- `ek_PKE = dk[1152 : 2336]`. -/
def dkEk (dk : List Byte) : List Byte := (dk.drop 1152).take 1184

/-- `h = dk[2336 : 2368]`. -/
def dkH (dk : List Byte) : List Byte := (dk.drop 2336).take 32

/-- `z = dk[2368 : 2400]`. -/
def dkZ (dk : List Byte) : List Byte := (dk.drop 2368).take 32

/-- `m' = K-PKE.Decrypt(dk_PKE, c)`. -/
def decM (dk c : List Byte) : List Byte := kpkeDecrypt mlKem768 (dkPke dk) c

/-- `ML-KEM.Decaps_internal(dk, c)` of ML-KEM-768: `(K', r') = G(m' ‖ h)`,
`c'` the re-encryption of `m'` with `r'`, and the key `K'` if `c = c'`, and
`K̄ = J(z ‖ c)` otherwise. -/
theorem decapsInternal768 (iters : Nat) (dk c : List Byte) :
    decapsInternal mlKem768 iters dk c =
      (kpkeEncrypt mlKem768 iters (dkEk dk) (decM dk c) (G (decM dk c ++ dkH dk)).2).map fun c' =>
        if c = c' then (G (decM dk c ++ dkH dk)).1 else J (dkZ dk ++ c) := by
  show (kpkeEncrypt mlKem768 iters (dkEk dk) (decM dk c) (G (decM dk c ++ dkH dk)).2).bind
      (fun c' => some (if c ≠ c' then J (dkZ dk ++ c) else (G (decM dk c ++ dkH dk)).1)) = _
  cases kpkeEncrypt mlKem768 iters (dkEk dk) (decM dk c) (G (decM dk c ++ dkH dk)).2 with
  | none => rfl
  | some c' =>
    rw [Option.bind_some, Option.map_some]
    by_cases h : c = c'
    · rw [ite_eq_right (fun h' : c ≠ c' => h' h), ite_eq_left h]
    · rw [ite_eq_left h, ite_eq_right h]

/-- Two byte strings of the same length are equal exactly when the OR of
the XORs of their bytes is 0: the comparison of `c` and `c'` in constant
time. -/
theorem eq_iff_foldl_or_xor : ∀ {c c' : List Byte}, c.length = c'.length →
    (c = c' ↔ (List.zipWith (· ^^^ ·) c c').foldl (· ||| ·) 0 = 0) := by
  suffices h : ∀ {c c' : List Byte}, c.length = c'.length → ∀ acc : Byte,
      (List.zipWith (· ^^^ ·) c c').foldl (· ||| ·) acc = 0 ↔ acc = 0 ∧ c = c' by
    intro c c' hl
    rw [h hl 0]
    simp
  intro c
  induction c with
  | nil => intro c' hl acc; cases c' <;> simp_all
  | cons x c ih =>
    intro c' hl acc
    cases c' with
    | nil => simp at hl
    | cons y c' =>
      simp only [List.zipWith_cons_cons, List.foldl_cons, List.cons.injEq]
      rw [ih (by simpa using hl)]
      constructor
      · rintro ⟨h₁, h₂⟩
        obtain ⟨h₃, h₄⟩ := BitVec.or_eq_zero_iff.mp h₁
        exact ⟨h₃, BitVec.xor_eq_zero_iff.mp h₄, h₂⟩
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨BitVec.or_eq_zero_iff.mpr ⟨h₁, BitVec.xor_eq_zero_iff.mpr h₂⟩, h₃⟩

end VG.Proof.MlKem
