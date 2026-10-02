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

What a caller of `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze`
(`Spec/Sha3/Contract.lean`) needs to conclude that it computed `H`, `J`, `G`,
`PRF` or `XOF` (§4.1): from the all-zero state, which represents the empty
message (`repr_nil`), absorbing the pieces of the message, padding with the
suffix of the function (`sha3Suffix32`, `shakeSuffix32`), and squeezing from
position 0 gives the function (`H_eq`, `J_eq`, `G_eq`, `prf_eq`, `xof_eq`, as
`squeezeFrom` of the padded state `padded`); and output squeezed in pieces is
the concatenation (`squeezeFrom_append`). Byte `p` of the XOF output is the
same whatever the length asked for (`xof_getD`, `xofByte`).
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

/-- Output from `p + a` of two states whose outputs from `p` and `c` agree. -/
theorem squeezeFrom_shift {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) {S P : State}
    {p c : Nat} (h : ∀ d, squeezeFrom rate S p d = squeezeFrom rate P c d) (a d : Nat) :
    squeezeFrom rate S (p + a) d = squeezeFrom rate P (c + a) d := by
  have e : ∀ (T : State) (x : Nat), squeezeFrom rate T (x + a) d = (squeezeFrom rate T x (a + d)).drop a :=
    fun T x => by rw [← squeezeFrom_append hr hr' T x a d, List.drop_left' (length_squeezeFrom hr hr' T x a)]
  rw [e S p, e P c, h]

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

`SampleNTT` (Algorithm 7) as the loop an implementation runs over the 3-byte
chunks of the XOF output (`xofByte`, above): `sampleAfter a out t` is the list
of coefficients accepted after the first `t` chunks, which stops growing once
it has 256 (`sampleStepCap`). An implementation that bounds the loop by
`iters` iterations and stops after `t ≤ iters` chunks with 256 coefficients
computes `sampleNTT iters B` (`sampleNTT_of_full`); one that reaches the bound
with fewer has `sampleNTT iters B = none` (`sampleNTT_none`).

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
# ML-KEM: K-PKE and the internal algorithms as polynomial steps

K-PKE.KeyGen, K-PKE.Encrypt, K-PKE.Decrypt (Algorithms 13–15) and the internal
algorithms (Algorithms 16–18) restated, for any parameter set `p` with
`η₁ = η₂ = 2` (ML-KEM-768 and ML-KEM-1024), as the sequence of calls of the
polynomial primitives (`Spec/MlKem/Poly.lean`) an implementation makes, so
that a proof of the top-level functions chains the primitives' contracts:

* `dotK a b k = (⋯(a₀ ×_T b₀ + a₁ ×_T b₁) + ⋯) + a_{k-1} ×_T b_{k-1}`,
  accumulated left to right with `add` (`dot_eq_dotK`), and `catK f k`
  the concatenation `f 0 ‖ ⋯ ‖ f (k - 1)`, both instances of `foldK`, which
  unfolds for a literal `k` to the explicit sum or concatenation;
* the matrix `Â` from the `k²` `SampleNTT`s (`sampleMatrix_some`,
  `sampleMatrix_none`);
* K-PKE.KeyGen: `t̂[i] = dotK (Â[i]) ŝ k + ê[i]`,
  `ek = ByteEncode₁₂(t̂[0]) ‖ … ‖ ρ`, `dk = ByteEncode₁₂(ŝ[0]) ‖ …`
  (`KPke.kpkeKeyGen_some`, `KPke.kpkeKeyGen_none`);
* K-PKE.Encrypt: `u[i] = NTT⁻¹(dotK (Â[·][i]) ŷ k) + e₁[i]`,
  `v = NTT⁻¹(dotK t̂ ŷ k) + e₂ + μ`, the ciphertext the compressed encodings
  of `u[0]`, …, `u[k-1]` and `v` (`KPke.kpkeEncrypt_some`,
  `KPke.kpkeEncrypt_none`);
* K-PKE.Decrypt (`KPke.kpkeDecrypt_eq`);
* the internal algorithms, and the layout of the decapsulation key
  (`KPke.keyGenInternal_eq`, `KPke.encapsInternal_eq`,
  `KPke.decapsInternal_eq`, `KPke.ekRho_dkEk`): decapsulation selects
  between `K'` and `K̄` by whether `c = c'`, which `eq_iff_foldl_or_xor`
  computes without branching.

The names of ML-KEM-768 (`kgRho`, `ekPKE768`, `kpkeKeyGen768_some`, …) and of
ML-KEM-1024 (`KPke1024.lean`) are these for `mlKem768` and `mlKem1024`.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

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

/-- `SamplePolyCBD₂(PRF₂(s, N))`. -/
def cbd (s : List Byte) (N : Nat) : Poly := samplePolyCBD 2 (prf 2 s (BitVec.ofNat 8 N))

/-- `((L.take N).drop s).take c = (L.drop s).take c` when `s + c ≤ N`. -/
theorem slice_take {α : Type} (L : List α) {N s c : Nat} (h : s + c ≤ N) :
    ((L.take N).drop s).take c = (L.drop s).take c := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- `t̂[i] = ByteDecode₁₂(ek[384i : 384i + 384])`. -/
def ekT (ek : List Byte) (i : Nat) : Poly := decode12 ((ek.drop (384 * i)).take 384)

/-- `ŷ[j] = NTT(SamplePolyCBD₂(PRF₂(r, j)))`. -/
def encY (r : List Byte) (j : Nat) : Poly := ntt (cbd r j)

/-- `ŝ[i] = ByteDecode₁₂(dk[384i : 384i + 384])`. -/
def dcS (dk : List Byte) (i : Nat) : Poly := decode12 ((dk.drop (384 * i)).take 384)


/-! ## Sums of products -/

namespace KPke

/-- `f 0 ⊕ f 1 ⊕ ⋯ ⊕ f (k - 1)` for `⊕ = op`, combined left to right from
`f 0`, and `z` for `k = 0`: for a literal `k`, it unfolds to the explicit
expression. -/
def foldK {α : Type} (op : α → α → α) (z : α) (f : Nat → α) : Nat → α
  | 0 => z
  | 1 => f 0
  | k + 2 => op (foldK op z f (k + 1)) (f (k + 1))

theorem foldK_succ {α : Type} {op : α → α → α} {z : α} (h : ∀ x, op z x = x) (f : Nat → α) :
    ∀ k, foldK op z f (k + 1) = op (foldK op z f k) (f k)
  | 0 => (h (f 0)).symm
  | _ + 1 => rfl

/-- `∑_{j<k} a j ×_{T_q} b j`, accumulated left to right with `add`. -/
abbrev dotK (a b : Nat → Poly) (k : Nat) : Poly := foldK add zero (fun j => multiplyNTTs (a j) (b j)) k

/-- `f 0 ‖ f 1 ‖ ⋯ ‖ f (k - 1)`. -/
abbrev catK (f : Nat → List Byte) (k : Nat) : List Byte := foldK (· ++ ·) [] f k

theorem dot_eq_dotK (a b : Nat → Poly) :
    ∀ k, dot ((List.range k).map a) ((List.range k).map b) = dotK a b k
  | 0 => rfl
  | k + 1 => by
    rw [dotK, foldK_succ zero_add_poly, ← dotK, ← dot_eq_dotK a b k]
    simp only [dot, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [List.zipWith_append (by simp), List.foldl_append]
    rfl

theorem catK_eq (f : Nat → List Byte) : ∀ k, catK f k = (List.range k).flatMap f
  | 0 => rfl
  | k + 1 => by
    rw [catK, foldK_succ List.nil_append, ← catK, catK_eq f k, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

theorem catK_length {f : Nat → List Byte} {c : Nat} (hf : ∀ i, (f i).length = c) (k : Nat) :
    (catK f k).length = c * k := by
  rw [catK_eq, length_flatMap_const f hf, List.length_range]

/-! ## Vectors and matrices -/

theorem addVec_map {α : Type} (f g : α → Poly) :
    ∀ L : List α, addVec (L.map f) (L.map g) = L.map fun x => add (f x) (g x)
  | [] => rfl
  | x :: L => by simp only [addVec, List.map_cons, List.zipWith_cons_cons] at *; rw [← addVec, addVec_map f g L]

theorem mulMatVec_matrix (k : Nat) (a : Nat → Nat → Poly) (u : Nat → Poly) :
    mulMatVec (matrix k a) ((List.range k).map u) = (List.range k).map fun i => dotK (a i) u k := by
  simp only [mulMatVec, matrix, List.map_map]
  exact List.map_congr_left fun i _ => dot_eq_dotK (a i) u k

theorem mulMatTVec_matrix (k : Nat) (a : Nat → Nat → Poly) (u : Nat → Poly) :
    mulMatTVec k (matrix k a) ((List.range k).map u) =
      (List.range k).map fun i => dotK (fun j => a j i) u k := by
  refine List.map_congr_left fun i hi => ?_
  rw [← dot_eq_dotK]
  refine congrArg (dot · _) ?_
  simp only [matrix, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (List.mem_range.mp hi), Option.map_some, Option.getD_some]

/-- `k` samples `SamplePolyCBD₂(PRF₂(s, N₀ + i))`. -/
theorem sampleVec_two {η : Nat} (hη : η = 2) (k : Nat) (s : List Byte) (N₀ : Nat) :
    sampleVec k η s N₀ = (List.range k).map fun i => cbd s (N₀ + i) := by
  subst hη; rfl

theorem map_ntt_sampleVec {η : Nat} (hη : η = 2) (k : Nat) (s : List Byte) :
    (sampleVec k η s 0).map ntt = (List.range k).map fun j => ntt (cbd s j) := by
  rw [sampleVec_two hη, List.map_map]
  exact List.map_congr_left fun j _ => by rw [Function.comp, Nat.zero_add]

/-! ## K-PKE.KeyGen -/

variable (p : Params)

/-- `ρ` of K-PKE.KeyGen(d): the first half of `G(d ‖ k)`. -/
def kgRho (d : List Byte) : List Byte := (G (d ++ [BitVec.ofNat 8 p.k])).1

/-- `σ` of K-PKE.KeyGen(d): the second half of `G(d ‖ k)`. -/
def kgSigma (d : List Byte) : List Byte := (G (d ++ [BitVec.ofNat 8 p.k])).2

/-- `ŝ[j] = NTT(SamplePolyCBD₂(PRF₂(σ, j)))`. -/
def kgS (d : List Byte) (j : Nat) : Poly := ntt (cbd (kgSigma p d) j)

/-- `ê[i] = NTT(SamplePolyCBD₂(PRF₂(σ, k + i)))`. -/
def kgE (d : List Byte) (i : Nat) : Poly := ntt (cbd (kgSigma p d) (p.k + i))

/-- `t̂[i] = Â[i] ∘ ŝ + ê[i]`. -/
def kgT (a : Nat → Nat → Poly) (d : List Byte) (i : Nat) : Poly := add (dotK (a i) (kgS p d) p.k) (kgE p d i)

/-- `ek_PKE = ByteEncode₁₂(t̂[0]) ‖ ⋯ ‖ ByteEncode₁₂(t̂[k - 1]) ‖ ρ`. -/
def ekPKE (a : Nat → Nat → Poly) (d : List Byte) : List Byte :=
  catK (fun i => encode12 (kgT p a d i)) p.k ++ kgRho p d

/-- `dk_PKE = ByteEncode₁₂(ŝ[0]) ‖ ⋯ ‖ ByteEncode₁₂(ŝ[k - 1])`. -/
def dkPKE (d : List Byte) : List Byte := catK (fun j => encode12 (kgS p d j)) p.k

theorem keyGenRho_eq (d : List Byte) : keyGenRho p d = kgRho p d := rfl

variable {p}

private theorem kpkeKeyGen_eq (iters : Nat) (d : List Byte) :
    kpkeKeyGen p iters d =
      (sampleMatrix p.k iters (kgRho p d)).bind fun A =>
        some (encodeVec (addVec (mulMatVec A ((sampleVec p.k p.η₁ (kgSigma p d) 0).map ntt))
          ((sampleVec p.k p.η₁ (kgSigma p d) p.k).map ntt)) ++ kgRho p d,
          encodeVec ((sampleVec p.k p.η₁ (kgSigma p d) 0).map ntt)) := by
  rfl

theorem kpkeKeyGen_some (hη : p.η₁ = 2) {iters : Nat} {d : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < p.k, ∀ j < p.k, sampleNTT iters (matSeed (kgRho p d) i j) = some (a i j)) :
    kpkeKeyGen p iters d = some (ekPKE p a d, dkPKE p d) := by
  rw [kpkeKeyGen_eq, sampleMatrix_some h, Option.bind_some, map_ntt_sampleVec hη, sampleVec_two hη,
    List.map_map, mulMatVec_matrix, addVec_map, encodeVec, encodeVec, List.flatMap_map, List.flatMap_map,
    ekPKE, dkPKE, catK_eq, catK_eq]
  rfl

theorem kpkeKeyGen_none {iters : Nat} {d : List Byte} {i j : Nat} (hi : i < p.k) (hj : j < p.k)
    (h : sampleNTT iters (matSeed (kgRho p d) i j) = none) : kpkeKeyGen p iters d = none := by
  rw [kpkeKeyGen_eq, sampleMatrix_none hi hj h]; rfl

theorem ekPKE_length (a : Nat → Nat → Poly) (d : List Byte) : (ekPKE p a d).length = p.ekLen := by
  rw [ekPKE, List.length_append, catK_length fun _ => encode12_length _, kgRho, G_fst_length]; rfl

theorem dkPKE_length (d : List Byte) : (dkPKE p d).length = 384 * p.k :=
  catK_length (fun _ => encode12_length _) p.k

/-! ## K-PKE.Encrypt -/

variable (p)

/-- `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, with `e₁[i] = SamplePolyCBD₂(PRF₂(r, k + i))`. -/
def encU (a : Nat → Nat → Poly) (r : List Byte) (i : Nat) : Poly :=
  add (nttInv (dotK (fun j => a j i) (encY r) p.k)) (cbd r (p.k + i))

/-- `v = NTT⁻¹(t̂ ∘ ŷ) + e₂ + μ`, with `e₂ = SamplePolyCBD₂(PRF₂(r, 2k))` and
`μ = Decompress₁(ByteDecode₁(m))`. -/
def encV (ek m r : List Byte) : Poly :=
  add (add (nttInv (dotK (ekT ek) (encY r) p.k)) (cbd r (2 * p.k))) (decodeDecompress 1 m)

/-- The ciphertext: `ByteEncode_{d_u}(Compress_{d_u}(u[i]))` for `i < k`, then
`ByteEncode_{d_v}(Compress_{d_v}(v))`. -/
def ct (a : Nat → Nat → Poly) (ek m r : List Byte) : List Byte :=
  catK (fun i => compressEncode p.du (encU p a r i)) p.k ++ compressEncode p.dv (encV p ek m r)

variable {p}

theorem ct_length (a : Nat → Nat → Poly) (ek m r : List Byte) : (ct p a ek m r).length = p.ctLen := by
  rw [ct, List.length_append, catK_length fun _ => compressEncode_length _ _, compressEncode_length,
    Params.ctLen, Nat.mul_add, Nat.mul_assoc]

private theorem kpkeEncrypt_eq (iters : Nat) (ek m r : List Byte) :
    kpkeEncrypt p iters ek m r =
      (sampleMatrix p.k iters (ekRho p ek)).bind fun A =>
        some ((addVec ((mulMatTVec p.k A ((sampleVec p.k p.η₁ r 0).map ntt)).map nttInv)
            (sampleVec p.k p.η₂ r p.k)).flatMap (compressEncode p.du) ++
          compressEncode p.dv (add (add (nttInv (dot (decodeVec p.k (ek.take (384 * p.k)))
            ((sampleVec p.k p.η₁ r 0).map ntt))) (samplePolyCBD p.η₂ (prf p.η₂ r (BitVec.ofNat 8 (2 * p.k)))))
            (decodeDecompress 1 m))) := by
  rfl

/-- `t̂ = ByteDecode₁₂(ek[384i : 384i + 384])` for `i < k`. -/
theorem decodeVec_take (k : Nat) (ek : List Byte) :
    decodeVec k (ek.take (384 * k)) = (List.range k).map (ekT ek) :=
  List.map_congr_left fun i hi => by
    rw [ekT, slice_take ek (show 384 * i + 384 ≤ 384 * k by have := List.mem_range.mp hi; omega)]

theorem kpkeEncrypt_some (hη : p.η₁ = 2 ∧ p.η₂ = 2) {iters : Nat} {ek m r : List Byte}
    {a : Nat → Nat → Poly} (h : ∀ i < p.k, ∀ j < p.k, sampleNTT iters (matSeed (ekRho p ek) i j) = some (a i j)) :
    kpkeEncrypt p iters ek m r = some (ct p a ek m r) := by
  rw [kpkeEncrypt_eq, sampleMatrix_some h, Option.bind_some, decodeVec_take, map_ntt_sampleVec hη.1,
    sampleVec_two hη.2, mulMatTVec_matrix, List.map_map, addVec_map, List.flatMap_map, dot_eq_dotK, hη.2,
    ct, catK_eq]
  rfl

theorem kpkeEncrypt_none {iters : Nat} {ek m r : List Byte} {i j : Nat} (hi : i < p.k) (hj : j < p.k)
    (h : sampleNTT iters (matSeed (ekRho p ek) i j) = none) :
    kpkeEncrypt p iters ek m r = none := by
  rw [kpkeEncrypt_eq, sampleMatrix_none hi hj h]; rfl

/-! ## K-PKE.Decrypt -/

variable (p)

/-- `u'[i] = Decompress_{d_u}(ByteDecode_{d_u}(c[32d_u·i : 32d_u·(i + 1)]))`. -/
def dcU (c : List Byte) (i : Nat) : Poly := decodeDecompress p.du ((c.drop (32 * p.du * i)).take (32 * p.du))

/-- `v' = Decompress_{d_v}(ByteDecode_{d_v}(c[32d_u·k : 32(d_u·k + d_v)]))`. -/
def dcV (c : List Byte) : Poly := decodeDecompress p.dv ((c.drop (32 * p.du * p.k)).take (32 * p.dv))

/-- K-PKE.Decrypt: `w = v' - NTT⁻¹(ŝ ∘ NTT(u'))`, and
`m = ByteEncode₁(Compress₁(w))`. -/
theorem kpkeDecrypt_eq (dk c : List Byte) :
    kpkeDecrypt p dk c =
      compressEncode 1 (sub (dcV p c) (nttInv (dotK (dcS dk) (fun i => ntt (dcU p c i)) p.k))) := by
  have e : kpkeDecrypt p dk c = compressEncode 1 (sub (dcV p c)
      (nttInv (dot ((List.range p.k).map (dcS dk)) ((List.range p.k).map fun i =>
        ntt (decodeDecompress p.du (((c.take (32 * p.du * p.k)).drop (32 * p.du * i)).take (32 * p.du))))))) := by
    simp only [kpkeDecrypt, List.map_map]; rfl
  rw [e, ← dot_eq_dotK]
  refine congrArg (fun L => compressEncode 1 (sub _ (nttInv (dot _ L)))) (List.map_congr_left fun i hi => ?_)
  rw [dcU, slice_take c (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (List.mem_range.mp hi))]

/-! ## The internal algorithms -/

/-- `ML-KEM.KeyGen_internal(d, z)`: `dk = dk_PKE ‖ ek ‖ H(ek) ‖ z`. -/
theorem keyGenInternal_eq (iters : Nat) (d z : List Byte) :
    keyGenInternal p iters d z = (kpkeKeyGen p iters d).map fun k => (k.1, k.2 ++ k.1 ++ H k.1 ++ z) := by
  simp only [keyGenInternal]
  cases kpkeKeyGen p iters d <;> rfl

/-- `ML-KEM.Encaps_internal(ek, m)`: `(K, r) = G(m ‖ H(ek))`, and the
ciphertext of K-PKE.Encrypt with `r`. -/
theorem encapsInternal_eq (iters : Nat) (ek m : List Byte) :
    encapsInternal p iters ek m =
      (kpkeEncrypt p iters ek m (G (m ++ H ek)).2).map fun c => ((G (m ++ H ek)).1, c) := by
  simp only [encapsInternal]
  cases kpkeEncrypt p iters ek m (G (m ++ H ek)).2 <;> rfl

/-- `dk_PKE = dk[0 : 384k]`. -/
def dkPke (dk : List Byte) : List Byte := dk.take (384 * p.k)

/-- `ek_PKE = dk[384k : 768k + 32]`. -/
def dkEk (dk : List Byte) : List Byte := (dk.drop (384 * p.k)).take (384 * p.k + 32)

/-- `h = dk[768k + 32 : 768k + 64]`. -/
def dkH (dk : List Byte) : List Byte := (dk.drop (768 * p.k + 32)).take 32

/-- `z = dk[768k + 64 : 768k + 96]`. -/
def dkZ (dk : List Byte) : List Byte := (dk.drop (768 * p.k + 64)).take 32

/-- `m' = K-PKE.Decrypt(dk_PKE, c)`. -/
def decM (dk c : List Byte) : List Byte := kpkeDecrypt p (dkPke p dk) c

theorem decM_length (dk c : List Byte) : (decM p dk c).length = 32 := compressEncode_length 1 _

/-- `ρ` of the encapsulation key in `dk`. -/
theorem ekRho_dkEk (dk : List Byte) : ekRho p (dkEk p dk) = dkRho p dk := by
  simp only [ekRho, dkRho, dkEk, List.drop_take, List.drop_drop, List.take_take]
  rw [show 384 * p.k + 384 * p.k = 768 * p.k by omega, show 384 * p.k + 32 - 384 * p.k = 32 by omega,
    Nat.min_self]

/-- `ML-KEM.Decaps_internal(dk, c)`: `(K', r') = G(m' ‖ h)`, `c'` the
re-encryption of `m'` with `r'`, and the key `K'` if `c = c'`, and
`K̄ = J(z ‖ c)` otherwise. -/
theorem decapsInternal_eq (iters : Nat) (dk c : List Byte) :
    decapsInternal p iters dk c =
      (kpkeEncrypt p iters (dkEk p dk) (decM p dk c) (G (decM p dk c ++ dkH p dk)).2).map fun c' =>
        if c = c' then (G (decM p dk c ++ dkH p dk)).1 else J (dkZ p dk ++ c) := by
  show (kpkeEncrypt p iters (dkEk p dk) (decM p dk c) (G (decM p dk c ++ dkH p dk)).2).bind
      (fun c' => some (if c ≠ c' then J (dkZ p dk ++ c) else (G (decM p dk c ++ dkH p dk)).1)) = _
  cases kpkeEncrypt p iters (dkEk p dk) (decM p dk c) (G (decM p dk c ++ dkH p dk)).2 with
  | none => rfl
  | some c' =>
    rw [Option.bind_some, Option.map_some]
    by_cases h : c = c'
    · rw [ite_eq_right (fun h' : c ≠ c' => h' h), ite_eq_left h]
    · rw [ite_eq_left h, ite_eq_right h]

variable {p}

/-- The decapsulation key `dk_PKE ‖ ek ‖ H(ek) ‖ z` that key generation
writes, of `768k + 96` bytes for a 32-byte `z`. -/
theorem dk_length (a : Nat → Nat → Poly) (d z : List Byte) (hz : z.length = 32) :
    (dkPKE p d ++ ekPKE p a d ++ H (ekPKE p a d) ++ z).length = p.dkLen := by
  simp only [List.length_append, dkPKE_length, ekPKE_length, H_length, hz, Params.ekLen, Params.dkLen]
  omega

end KPke

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

/-! ## ML-KEM-768

The names the proofs of each target use, for `mlKem768`. -/

/-- `∑_{j<3} a j ×_{T_q} b j`. -/
abbrev dot3 (a b : Nat → Poly) : Poly := KPke.dotK a b 3

abbrev kgRho (d : List Byte) : List Byte := KPke.kgRho mlKem768 d
abbrev kgSigma (d : List Byte) : List Byte := KPke.kgSigma mlKem768 d
abbrev kgS (d : List Byte) (j : Nat) : Poly := KPke.kgS mlKem768 d j
abbrev kgE (d : List Byte) (i : Nat) : Poly := KPke.kgE mlKem768 d i
abbrev kgT (a : Nat → Nat → Poly) (d : List Byte) (i : Nat) : Poly := KPke.kgT mlKem768 a d i
abbrev ekPKE768 (a : Nat → Nat → Poly) (d : List Byte) : List Byte := KPke.ekPKE mlKem768 a d
abbrev dkPKE768 (d : List Byte) : List Byte := KPke.dkPKE mlKem768 d
abbrev encU (a : Nat → Nat → Poly) (r : List Byte) (i : Nat) : Poly := KPke.encU mlKem768 a r i
abbrev encV (ek m r : List Byte) : Poly := KPke.encV mlKem768 ek m r
abbrev ct768 (a : Nat → Nat → Poly) (ek m r : List Byte) : List Byte := KPke.ct mlKem768 a ek m r
abbrev dcU (c : List Byte) (i : Nat) : Poly := KPke.dcU mlKem768 c i
abbrev dcV (c : List Byte) : Poly := KPke.dcV mlKem768 c
abbrev dkPke (dk : List Byte) : List Byte := KPke.dkPke mlKem768 dk
abbrev dkEk (dk : List Byte) : List Byte := KPke.dkEk mlKem768 dk
abbrev dkH (dk : List Byte) : List Byte := KPke.dkH mlKem768 dk
abbrev dkZ (dk : List Byte) : List Byte := KPke.dkZ mlKem768 dk
abbrev decM (dk c : List Byte) : List Byte := KPke.decM mlKem768 dk c

theorem ekPKE768_eq (a : Nat → Nat → Poly) (d : List Byte) :
    ekPKE768 a d = encode12 (kgT a d 0) ++ encode12 (kgT a d 1) ++ encode12 (kgT a d 2) ++ kgRho d := rfl

theorem ct768_eq (a : Nat → Nat → Poly) (ek m r : List Byte) :
    ct768 a ek m r = compressEncode 10 (encU a r 0) ++ compressEncode 10 (encU a r 1) ++
      compressEncode 10 (encU a r 2) ++ compressEncode 4 (encV ek m r) := rfl

theorem dkPKE768_eq (d : List Byte) : dkPKE768 d = encode12 (kgS d 0) ++ encode12 (kgS d 1) ++ encode12 (kgS d 2) :=
  rfl

theorem kpkeKeyGen768_some {iters : Nat} {d : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 3, ∀ j < 3, sampleNTT iters (matSeed (kgRho d) i j) = some (a i j)) :
    kpkeKeyGen mlKem768 iters d = some (ekPKE768 a d, dkPKE768 d) :=
  KPke.kpkeKeyGen_some rfl h

theorem kpkeKeyGen768_none {iters : Nat} {d : List Byte} {i j : Nat} (hi : i < 3) (hj : j < 3)
    (h : sampleNTT iters (matSeed (kgRho d) i j) = none) : kpkeKeyGen mlKem768 iters d = none :=
  KPke.kpkeKeyGen_none hi hj h

theorem kpkeEncrypt768_some {iters : Nat} {ek m r : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 3, ∀ j < 3, sampleNTT iters (matSeed (ekRho mlKem768 ek) i j) = some (a i j)) :
    kpkeEncrypt mlKem768 iters ek m r = some (ct768 a ek m r) :=
  KPke.kpkeEncrypt_some ⟨rfl, rfl⟩ h

theorem kpkeEncrypt768_none {iters : Nat} {ek m r : List Byte} {i j : Nat} (hi : i < 3) (hj : j < 3)
    (h : sampleNTT iters (matSeed (ekRho mlKem768 ek) i j) = none) :
    kpkeEncrypt mlKem768 iters ek m r = none :=
  KPke.kpkeEncrypt_none hi hj h

theorem kpkeDecrypt768 (dk c : List Byte) :
    kpkeDecrypt mlKem768 dk c =
      compressEncode 1 (sub (dcV c) (nttInv (dot3 (dcS dk) fun i => ntt (dcU c i)))) :=
  KPke.kpkeDecrypt_eq mlKem768 dk c

theorem keyGenInternal768 (iters : Nat) (d z : List Byte) :
    keyGenInternal mlKem768 iters d z =
      (kpkeKeyGen mlKem768 iters d).map fun k => (k.1, k.2 ++ k.1 ++ H k.1 ++ z) :=
  KPke.keyGenInternal_eq mlKem768 iters d z

theorem encapsInternal768 (iters : Nat) (ek m : List Byte) :
    encapsInternal mlKem768 iters ek m =
      (kpkeEncrypt mlKem768 iters ek m (G (m ++ H ek)).2).map fun c => ((G (m ++ H ek)).1, c) :=
  KPke.encapsInternal_eq mlKem768 iters ek m

theorem decapsInternal768 (iters : Nat) (dk c : List Byte) :
    decapsInternal mlKem768 iters dk c =
      (kpkeEncrypt mlKem768 iters (dkEk dk) (decM dk c) (G (decM dk c ++ dkH dk)).2).map fun c' =>
        if c = c' then (G (decM dk c ++ dkH dk)).1 else J (dkZ dk ++ c) :=
  KPke.decapsInternal_eq mlKem768 iters dk c

end VG.Proof.MlKem
