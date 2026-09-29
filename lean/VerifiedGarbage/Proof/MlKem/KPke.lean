import VerifiedGarbage.Proof.MlKem.Sample
import VerifiedGarbage.Proof.MlKem.Encode

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
