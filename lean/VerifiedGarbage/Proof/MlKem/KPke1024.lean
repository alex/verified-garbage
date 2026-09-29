import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM-1024: K-PKE and the internal algorithms as polynomial steps

Untrusted: everything here is checked by Lean. The analog of `KPke.lean` for
ML-KEM-1024 (`k = 4`, `η₁ = η₂ = 2`, `d_u = 11`, `d_v = 5`): K-PKE.KeyGen,
K-PKE.Encrypt, K-PKE.Decrypt (Algorithms 13–15) and the internal algorithms
(Algorithms 16–18) restated as the sequence of calls of the polynomial
primitives (`Spec/MlKem/Poly.lean`, and `Spec/MlKem/Contract1024.lean` for
the compression to 11 and 5 bits) an implementation makes:

* `dot4 a b = ((a₀ ×_T b₀ + a₁ ×_T b₁) + a₂ ×_T b₂) + a₃ ×_T b₃`,
  accumulated left to right with `add` (`dot_eq_dot4`);
* the matrix `Â` from the sixteen `SampleNTT`s (`sampleMatrix_some`,
  `sampleMatrix_none` of `KPke.lean`, for any `k`);
* K-PKE.KeyGen: `t̂[i] = dot4 (Â[i]) ŝ + ê[i]`,
  `ek = ByteEncode₁₂(t̂[0]) ‖ … ‖ ByteEncode₁₂(t̂[3]) ‖ ρ`,
  `dk = ByteEncode₁₂(ŝ[0]) ‖ …` (`kpkeKeyGen1024_some`, `kpkeKeyGen1024_none`);
* K-PKE.Encrypt: `u[i] = NTT⁻¹(dot4 (Â[·][i]) ŷ) + e₁[i]`,
  `v = NTT⁻¹(dot4 t̂ ŷ) + e₂ + μ`, the ciphertext the compressed encodings of
  `u[0]`, …, `u[3]` (352 bytes each) and `v` (160 bytes)
  (`kpkeEncrypt1024_some`, `kpkeEncrypt1024_none`);
* K-PKE.Decrypt (`kpkeDecrypt1024`);
* the internal algorithms, and the layout of the decapsulation key
  (`dk_PKE`, `ek`, `H(ek)` and `z` at bytes 0, 1536, 3104 and 3136)
  (`keyGenInternal1024`, `encapsInternal1024`, `decapsInternal1024`):
  decapsulation selects between `K'` and `K̄` by whether `c = c'`, which
  `eq_iff_foldl_or_xor` (`KPke.lean`) computes without branching.

The polynomials that do not depend on `k` are those of `KPke.lean`: `cbd`,
`matSeed`, `matrix`, `ekT`, `encY` and `dcS`. That a bigger bound on the
iterations of `SampleNTT` gives the same result, and `Outcome`, are
`Sample.lean`'s, for any parameter set (`keyGenInternal_mono`, …,
`outcome_of_min`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## Sums of products -/

/-- `∑_{j<4} a j ×_{T_q} b j`, accumulated left to right with `add`. -/
def dot4 (a b : Nat → Poly) : Poly :=
  add (add (add (multiplyNTTs (a 0) (b 0)) (multiplyNTTs (a 1) (b 1))) (multiplyNTTs (a 2) (b 2)))
    (multiplyNTTs (a 3) (b 3))

theorem list_range4 {α : Type} (a : Nat → α) : (List.range 4).map a = [a 0, a 1, a 2, a 3] := rfl

theorem dot_eq_dot4 (a b : Nat → Poly) : dot [a 0, a 1, a 2, a 3] [b 0, b 1, b 2, b 3] = dot4 a b := by
  simp only [dot, List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil,
    zero_add_poly, dot4]

/-! ## K-PKE.KeyGen -/

/-- `ρ` of K-PKE.KeyGen(d) of ML-KEM-1024: the first half of `G(d ‖ 4)`. -/
def kgRho1024 (d : List Byte) : List Byte := (G (d ++ [BitVec.ofNat 8 4])).1

/-- `σ` of K-PKE.KeyGen(d) of ML-KEM-1024: the second half of `G(d ‖ 4)`. -/
def kgSigma1024 (d : List Byte) : List Byte := (G (d ++ [BitVec.ofNat 8 4])).2

/-- `ŝ[j] = NTT(SamplePolyCBD₂(PRF₂(σ, j)))`. -/
def kgS1024 (d : List Byte) (j : Nat) : Poly := ntt (cbd (kgSigma1024 d) j)

/-- `ê[i] = NTT(SamplePolyCBD₂(PRF₂(σ, 4 + i)))`. -/
def kgE1024 (d : List Byte) (i : Nat) : Poly := ntt (cbd (kgSigma1024 d) (4 + i))

/-- `t̂[i] = Â[i] ∘ ŝ + ê[i]`. -/
def kgT1024 (a : Nat → Nat → Poly) (d : List Byte) (i : Nat) : Poly :=
  add (dot4 (a i) (kgS1024 d)) (kgE1024 d i)

/-- `ek_PKE = ByteEncode₁₂(t̂[0]) ‖ ⋯ ‖ ByteEncode₁₂(t̂[3]) ‖ ρ`. -/
def ekPKE1024 (a : Nat → Nat → Poly) (d : List Byte) : List Byte :=
  encode12 (kgT1024 a d 0) ++ encode12 (kgT1024 a d 1) ++ encode12 (kgT1024 a d 2) ++
    encode12 (kgT1024 a d 3) ++ kgRho1024 d

/-- `dk_PKE = ByteEncode₁₂(ŝ[0]) ‖ ⋯ ‖ ByteEncode₁₂(ŝ[3])`. -/
def dkPKE1024 (d : List Byte) : List Byte :=
  encode12 (kgS1024 d 0) ++ encode12 (kgS1024 d 1) ++ encode12 (kgS1024 d 2) ++ encode12 (kgS1024 d 3)

theorem kgRho1024_eq (d : List Byte) : keyGenRho mlKem1024 d = kgRho1024 d := rfl

private theorem kpkeKeyGen1024_eq (iters : Nat) (d : List Byte) :
    kpkeKeyGen mlKem1024 iters d =
      (sampleMatrix 4 iters (kgRho1024 d)).bind fun A =>
        some (encodeVec (addVec (mulMatVec A ((List.range 4).map (kgS1024 d)))
          ((List.range 4).map (kgE1024 d))) ++ kgRho1024 d,
          encodeVec ((List.range 4).map (kgS1024 d))) := by
  rfl

theorem kpkeKeyGen1024_some {iters : Nat} {d : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (kgRho1024 d) i j) = some (a i j)) :
    kpkeKeyGen mlKem1024 iters d = some (ekPKE1024 a d, dkPKE1024 d) := by
  rw [kpkeKeyGen1024_eq, sampleMatrix_some h, Option.bind_some]
  simp only [matrix, list_range4, mulMatVec, List.map_cons, List.map_nil, addVec,
    List.zipWith_cons_cons, List.zipWith_nil_left, encodeVec, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, ekPKE1024, dkPKE1024, kgT1024]
  rw [dot_eq_dot4, dot_eq_dot4, dot_eq_dot4, dot_eq_dot4]

theorem kpkeKeyGen1024_none {iters : Nat} {d : List Byte} {i j : Nat} (hi : i < 4) (hj : j < 4)
    (h : sampleNTT iters (matSeed (kgRho1024 d) i j) = none) : kpkeKeyGen mlKem1024 iters d = none := by
  rw [kpkeKeyGen1024_eq, sampleMatrix_none hi hj h]; rfl

theorem ekPKE1024_length (a : Nat → Nat → Poly) (d : List Byte) : (ekPKE1024 a d).length = 1568 := by
  simp only [ekPKE1024, List.length_append, encode12_length, kgRho1024, G_fst_length]

theorem dkPKE1024_length (d : List Byte) : (dkPKE1024 d).length = 1536 := by
  simp only [dkPKE1024, List.length_append, encode12_length]

/-! ## K-PKE.Encrypt -/

/-- `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, with `e₁[i] = SamplePolyCBD₂(PRF₂(r, 4 + i))`. -/
def encU1024 (a : Nat → Nat → Poly) (r : List Byte) (i : Nat) : Poly :=
  add (nttInv (dot4 (fun j => a j i) (encY r))) (cbd r (4 + i))

/-- `v = NTT⁻¹(t̂ ∘ ŷ) + e₂ + μ`, with `e₂ = SamplePolyCBD₂(PRF₂(r, 8))` and
`μ = Decompress₁(ByteDecode₁(m))`. -/
def encV1024 (ek m r : List Byte) : Poly :=
  add (add (nttInv (dot4 (ekT ek) (encY r))) (cbd r 8)) (decodeDecompress 1 m)

/-- The ciphertext: `ByteEncode₁₁(Compress₁₁(u[i]))` for `i < 4`, then
`ByteEncode₅(Compress₅(v))`. -/
def ct1024 (a : Nat → Nat → Poly) (ek m r : List Byte) : List Byte :=
  compressEncode 11 (encU1024 a r 0) ++ compressEncode 11 (encU1024 a r 1) ++
    compressEncode 11 (encU1024 a r 2) ++ compressEncode 11 (encU1024 a r 3) ++
    compressEncode 5 (encV1024 ek m r)

theorem ct1024_length (a : Nat → Nat → Poly) (ek m r : List Byte) :
    (ct1024 a ek m r).length = 1568 := by
  simp only [ct1024, List.length_append, compressEncode_length]

/-- `ρ = ek[1536 : 1568]`. -/
theorem ekRho1024 (ek : List Byte) : ekRho mlKem1024 ek = (ek.drop 1536).take 32 := rfl

private theorem kpkeEncrypt1024_eq (iters : Nat) (ek m r : List Byte) :
    kpkeEncrypt mlKem1024 iters ek m r =
      (sampleMatrix 4 iters (ekRho mlKem1024 ek)).bind fun A =>
        some ((addVec ((mulMatTVec 4 A ((List.range 4).map (encY r))).map nttInv)
            ((List.range 4).map fun i => cbd r (4 + i))).flatMap (compressEncode 11) ++
          compressEncode 5 (add (add (nttInv (dot (decodeVec 4 (ek.take 1536))
            ((List.range 4).map (encY r)))) (cbd r 8)) (decodeDecompress 1 m))) := by
  rfl

theorem decodeVec1024 (ek : List Byte) :
    decodeVec 4 (ek.take 1536) = [ekT ek 0, ekT ek 1, ekT ek 2, ekT ek 3] := by
  simp only [decodeVec, list_range4, ekT, slice_take ek (show 384 * 0 + 384 ≤ 1536 by decide),
    slice_take ek (show 384 * 1 + 384 ≤ 1536 by decide), slice_take ek (show 384 * 2 + 384 ≤ 1536 by decide),
    slice_take ek (show 384 * 3 + 384 ≤ 1536 by decide)]

theorem kpkeEncrypt1024_some {iters : Nat} {ek m r : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (ekRho mlKem1024 ek) i j) = some (a i j)) :
    kpkeEncrypt mlKem1024 iters ek m r = some (ct1024 a ek m r) := by
  rw [kpkeEncrypt1024_eq, sampleMatrix_some h, Option.bind_some, decodeVec1024]
  simp only [matrix, list_range4, mulMatTVec, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, addVec, List.zipWith_cons_cons, List.zipWith_nil_left, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc, ct1024, encU1024, encV1024, ← dot_eq_dot4]

theorem kpkeEncrypt1024_none {iters : Nat} {ek m r : List Byte} {i j : Nat} (hi : i < 4) (hj : j < 4)
    (h : sampleNTT iters (matSeed (ekRho mlKem1024 ek) i j) = none) :
    kpkeEncrypt mlKem1024 iters ek m r = none := by
  rw [kpkeEncrypt1024_eq, sampleMatrix_none hi hj h]; rfl

/-! ## K-PKE.Decrypt -/

/-- `u'[i] = Decompress₁₁(ByteDecode₁₁(c[352i : 352i + 352]))`. -/
def dcU1024 (c : List Byte) (i : Nat) : Poly := decodeDecompress 11 ((c.drop (352 * i)).take 352)

/-- `v' = Decompress₅(ByteDecode₅(c[1408 : 1568]))`. -/
def dcV1024 (c : List Byte) : Poly := decodeDecompress 5 ((c.drop 1408).take 160)

/-- K-PKE.Decrypt of ML-KEM-1024: `w = v' - NTT⁻¹(ŝ ∘ NTT(u'))`, and
`m = ByteEncode₁(Compress₁(w))`. -/
theorem kpkeDecrypt1024 (dk c : List Byte) :
    kpkeDecrypt mlKem1024 dk c =
      compressEncode 1 (sub (dcV1024 c) (nttInv (dot4 (dcS dk) fun i => ntt (dcU1024 c i)))) := by
  have e : kpkeDecrypt mlKem1024 dk c = compressEncode 1 (sub (decodeDecompress 5 ((c.drop 1408).take 160))
      (nttInv (dot (decodeVec 4 dk) (((List.range 4).map fun i =>
        decodeDecompress 11 (((c.take 1408).drop (352 * i)).take 352)).map ntt)))) := rfl
  rw [e, ← dot_eq_dot4]
  simp only [decodeVec, list_range4, List.map_cons, List.map_nil, dcV1024, dcS, dcU1024,
    slice_take c (show 352 * 0 + 352 ≤ 1408 by decide), slice_take c (show 352 * 1 + 352 ≤ 1408 by decide),
    slice_take c (show 352 * 2 + 352 ≤ 1408 by decide), slice_take c (show 352 * 3 + 352 ≤ 1408 by decide)]

/-! ## The internal algorithms -/

/-- `ML-KEM.KeyGen_internal(d, z)` of ML-KEM-1024: `dk = dk_PKE ‖ ek ‖ H(ek) ‖ z`. -/
theorem keyGenInternal1024 (iters : Nat) (d z : List Byte) :
    keyGenInternal mlKem1024 iters d z =
      (kpkeKeyGen mlKem1024 iters d).map fun k => (k.1, k.2 ++ k.1 ++ H k.1 ++ z) := by
  simp only [keyGenInternal]
  cases kpkeKeyGen mlKem1024 iters d <;> rfl

/-- `ML-KEM.Encaps_internal(ek, m)` of ML-KEM-1024: `(K, r) = G(m ‖ H(ek))`,
and the ciphertext of K-PKE.Encrypt with `r`. -/
theorem encapsInternal1024 (iters : Nat) (ek m : List Byte) :
    encapsInternal mlKem1024 iters ek m =
      (kpkeEncrypt mlKem1024 iters ek m (G (m ++ H ek)).2).map fun c => ((G (m ++ H ek)).1, c) := by
  simp only [encapsInternal]
  cases kpkeEncrypt mlKem1024 iters ek m (G (m ++ H ek)).2 <;> rfl

/-- `dk_PKE = dk[0 : 1536]`. -/
def dkPke1024 (dk : List Byte) : List Byte := dk.take 1536

/-- `ek_PKE = dk[1536 : 3104]`. -/
def dkEk1024 (dk : List Byte) : List Byte := (dk.drop 1536).take 1568

/-- `h = dk[3104 : 3136]`. -/
def dkH1024 (dk : List Byte) : List Byte := (dk.drop 3104).take 32

/-- `z = dk[3136 : 3168]`. -/
def dkZ1024 (dk : List Byte) : List Byte := (dk.drop 3136).take 32

/-- `ρ = dk[3072 : 3104]`, that of the encapsulation key in `dk`. -/
theorem dkRho1024 (dk : List Byte) : dkRho mlKem1024 dk = (dk.drop 3072).take 32 := rfl

/-- `m' = K-PKE.Decrypt(dk_PKE, c)`. -/
def decM1024 (dk c : List Byte) : List Byte := kpkeDecrypt mlKem1024 (dkPke1024 dk) c

theorem decM1024_length (dk c : List Byte) : (decM1024 dk c).length = 32 := by
  rw [decM1024, kpkeDecrypt1024, compressEncode_length]

/-- `ML-KEM.Decaps_internal(dk, c)` of ML-KEM-1024: `(K', r') = G(m' ‖ h)`,
`c'` the re-encryption of `m'` with `r'`, and the key `K'` if `c = c'`, and
`K̄ = J(z ‖ c)` otherwise. -/
theorem decapsInternal1024 (iters : Nat) (dk c : List Byte) :
    decapsInternal mlKem1024 iters dk c =
      (kpkeEncrypt mlKem1024 iters (dkEk1024 dk) (decM1024 dk c)
          (G (decM1024 dk c ++ dkH1024 dk)).2).map fun c' =>
        if c = c' then (G (decM1024 dk c ++ dkH1024 dk)).1 else J (dkZ1024 dk ++ c) := by
  show (kpkeEncrypt mlKem1024 iters (dkEk1024 dk) (decM1024 dk c) (G (decM1024 dk c ++ dkH1024 dk)).2).bind
      (fun c' => some (if c ≠ c' then J (dkZ1024 dk ++ c) else (G (decM1024 dk c ++ dkH1024 dk)).1)) = _
  cases kpkeEncrypt mlKem1024 iters (dkEk1024 dk) (decM1024 dk c) (G (decM1024 dk c ++ dkH1024 dk)).2 with
  | none => rfl
  | some c' =>
    rw [Option.bind_some, Option.map_some]
    by_cases h : c = c'
    · rw [ite_eq_right (fun h' : c ≠ c' => h' h), ite_eq_left h]
    · rw [ite_eq_left h, ite_eq_right h]

/-- The decapsulation key `dk_PKE ‖ ek ‖ H(ek) ‖ z` that key generation
writes, of 3168 bytes for a 32-byte `z`. -/
theorem dk1024_length (a : Nat → Nat → Poly) (d z : List Byte) (hz : z.length = 32) :
    (dkPKE1024 d ++ ekPKE1024 a d ++ H (ekPKE1024 a d) ++ z).length = 3168 := by
  simp only [List.length_append, dkPKE1024_length, ekPKE1024_length, H_length, hz]

end VG.Proof.MlKem
