import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM-1024: K-PKE and the internal algorithms as polynomial steps

The names the proofs of each target use for ML-KEM-1024 (`k = 4`,
`η₁ = η₂ = 2`, `d_u = 11`, `d_v = 5`): those of `KPke.lean`, which states
K-PKE and the internal algorithms for any parameter set, for `mlKem1024`.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- `∑_{j<4} a j ×_{T_q} b j`. -/
abbrev dot4 (a b : Nat → Poly) : Poly := KPke.dotK a b 4

abbrev kgRho1024 (d : List Byte) : List Byte := KPke.kgRho mlKem1024 d
abbrev kgSigma1024 (d : List Byte) : List Byte := KPke.kgSigma mlKem1024 d
abbrev kgS1024 (d : List Byte) (j : Nat) : Poly := KPke.kgS mlKem1024 d j
abbrev kgE1024 (d : List Byte) (i : Nat) : Poly := KPke.kgE mlKem1024 d i
abbrev kgT1024 (a : Nat → Nat → Poly) (d : List Byte) (i : Nat) : Poly := KPke.kgT mlKem1024 a d i
abbrev ekPKE1024 (a : Nat → Nat → Poly) (d : List Byte) : List Byte := KPke.ekPKE mlKem1024 a d
abbrev dkPKE1024 (d : List Byte) : List Byte := KPke.dkPKE mlKem1024 d
abbrev encU1024 (a : Nat → Nat → Poly) (r : List Byte) (i : Nat) : Poly := KPke.encU mlKem1024 a r i
abbrev encV1024 (ek m r : List Byte) : Poly := KPke.encV mlKem1024 ek m r
abbrev ct1024 (a : Nat → Nat → Poly) (ek m r : List Byte) : List Byte := KPke.ct mlKem1024 a ek m r
abbrev dcU1024 (c : List Byte) (i : Nat) : Poly := KPke.dcU mlKem1024 c i
abbrev dcV1024 (c : List Byte) : Poly := KPke.dcV mlKem1024 c
abbrev dkPke1024 (dk : List Byte) : List Byte := KPke.dkPke mlKem1024 dk
abbrev dkEk1024 (dk : List Byte) : List Byte := KPke.dkEk mlKem1024 dk
abbrev dkH1024 (dk : List Byte) : List Byte := KPke.dkH mlKem1024 dk
abbrev dkZ1024 (dk : List Byte) : List Byte := KPke.dkZ mlKem1024 dk
abbrev decM1024 (dk c : List Byte) : List Byte := KPke.decM mlKem1024 dk c

theorem ekPKE1024_eq (a : Nat → Nat → Poly) (d : List Byte) :
    ekPKE1024 a d = encode12 (kgT1024 a d 0) ++ encode12 (kgT1024 a d 1) ++ encode12 (kgT1024 a d 2) ++
      encode12 (kgT1024 a d 3) ++ kgRho1024 d := rfl

theorem ct1024_eq (a : Nat → Nat → Poly) (ek m r : List Byte) :
    ct1024 a ek m r = compressEncode 11 (encU1024 a r 0) ++ compressEncode 11 (encU1024 a r 1) ++
      compressEncode 11 (encU1024 a r 2) ++ compressEncode 11 (encU1024 a r 3) ++
      compressEncode 5 (encV1024 ek m r) := rfl

theorem dkPKE1024_eq (d : List Byte) :
    dkPKE1024 d = encode12 (kgS1024 d 0) ++ encode12 (kgS1024 d 1) ++ encode12 (kgS1024 d 2) ++
      encode12 (kgS1024 d 3) := rfl

theorem kpkeKeyGen1024_some {iters : Nat} {d : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (kgRho1024 d) i j) = some (a i j)) :
    kpkeKeyGen mlKem1024 iters d = some (ekPKE1024 a d, dkPKE1024 d) :=
  KPke.kpkeKeyGen_some rfl h

theorem kpkeKeyGen1024_none {iters : Nat} {d : List Byte} {i j : Nat} (hi : i < 4) (hj : j < 4)
    (h : sampleNTT iters (matSeed (kgRho1024 d) i j) = none) : kpkeKeyGen mlKem1024 iters d = none :=
  KPke.kpkeKeyGen_none hi hj h

theorem kpkeEncrypt1024_some {iters : Nat} {ek m r : List Byte} {a : Nat → Nat → Poly}
    (h : ∀ i < 4, ∀ j < 4, sampleNTT iters (matSeed (ekRho mlKem1024 ek) i j) = some (a i j)) :
    kpkeEncrypt mlKem1024 iters ek m r = some (ct1024 a ek m r) :=
  KPke.kpkeEncrypt_some ⟨rfl, rfl⟩ h

theorem kpkeEncrypt1024_none {iters : Nat} {ek m r : List Byte} {i j : Nat} (hi : i < 4) (hj : j < 4)
    (h : sampleNTT iters (matSeed (ekRho mlKem1024 ek) i j) = none) :
    kpkeEncrypt mlKem1024 iters ek m r = none :=
  KPke.kpkeEncrypt_none hi hj h

theorem kpkeDecrypt1024 (dk c : List Byte) :
    kpkeDecrypt mlKem1024 dk c =
      compressEncode 1 (sub (dcV1024 c) (nttInv (dot4 (dcS dk) fun i => ntt (dcU1024 c i)))) :=
  KPke.kpkeDecrypt_eq mlKem1024 dk c

theorem keyGenInternal1024 (iters : Nat) (d z : List Byte) :
    keyGenInternal mlKem1024 iters d z =
      (kpkeKeyGen mlKem1024 iters d).map fun k => (k.1, k.2 ++ k.1 ++ H k.1 ++ z) :=
  KPke.keyGenInternal_eq mlKem1024 iters d z

theorem encapsInternal1024 (iters : Nat) (ek m : List Byte) :
    encapsInternal mlKem1024 iters ek m =
      (kpkeEncrypt mlKem1024 iters ek m (G (m ++ H ek)).2).map fun c => ((G (m ++ H ek)).1, c) :=
  KPke.encapsInternal_eq mlKem1024 iters ek m

theorem decapsInternal1024 (iters : Nat) (dk c : List Byte) :
    decapsInternal mlKem1024 iters dk c =
      (kpkeEncrypt mlKem1024 iters (dkEk1024 dk) (decM1024 dk c)
          (G (decM1024 dk c ++ dkH1024 dk)).2).map fun c' =>
        if c = c' then (G (decM1024 dk c ++ dkH1024 dk)).1 else J (dkZ1024 dk ++ c) :=
  KPke.decapsInternal_eq mlKem1024 iters dk c

end VG.Proof.MlKem
