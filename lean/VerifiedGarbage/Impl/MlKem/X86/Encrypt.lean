import VerifiedGarbage.Impl.MlKem.X86.Kem

/-!
# ML-KEM on x86 (32-bit): K-PKE.Encrypt, in `scratch`

`encrypt L sc`: K-PKE.Encrypt(ek, m, r) (Algorithm 14), with every buffer in
`scratch` (argument `sc`, in `esi`) at the offsets of `L` (`Kem.lean`), which
encapsulation and decapsulation share.

The code is unrolled: `ŷ[N]` is `encYC L sc N` (`PRF`, CBD, NTT); `u[i]` is
`encRow L sc i`: the entries `Â[j, i]` for `j < k`, each sampled, masked and
multiplied by `ŷ[j]` and summed (`encEntry`), then `NTT⁻¹`, `e₁[i]` added and
the sum compressed to `d_u` bits into the ciphertext; and `v` is `encV`: the
products of `t̂[j]` (decoded from `ek`) and `ŷ[j]` summed, `NTT⁻¹`, `e₂` and `μ`
added, and the sum compressed to `d_v` bits into the ciphertext.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

variable (L : KemLay)

/-- `SamplePolyCBD₂(PRF₂(r, N))` into `scratch + o`. -/
def encCbd (sc N o : Nat) : Prog isa :=
  .seq (.block (st8 (L.eKR + 64) N)) <|
  .seq (hash1 sc L.eST L.eWK 136 0x1f ⟨sc, L.eKR + 32, 33⟩ ⟨sc, L.ePRF, 128⟩)
    (cbd2C sc ⟨sc, L.ePRF, 128⟩ ⟨sc, o, 1024⟩)

/-- `ŷ[N] = NTT(SamplePolyCBD₂(PRF₂(r, N)))`. -/
def encYC (sc N : Nat) : Prog isa :=
  .seq (encCbd L sc N (1024 * N)) (nttC sc ⟨sc, 1024 * N, 1024⟩ ⟨sc, L.eNS, 1024⟩)

/-- `Â[j, i] ← SampleNTT(ρ ‖ i ‖ j)`, masked, times `ŷ[j]`, added to `u[i]`
(written to it if `j = 0`). -/
def encEntry (sc i j : Nat) : Prog isa :=
  .seq (.block (st8 (L.eEK + L.p.ekLen) i)) <| .seq (.block (st8 (L.eEK + L.p.ekLen + 1) j)) <|
  .seq (sampleC sc ⟨sc, L.eEK + 384 * L.p.k, 34⟩ ⟨sc, L.eA, 1024⟩ ⟨sc, L.eSS, 2048⟩) <|
  .seq (maskA L.eACC L.eA) <|
  if j = 0 then mulC sc ⟨sc, L.eU, 1024⟩ ⟨sc, L.eA, 1024⟩ ⟨sc, 0, 1024⟩ ⟨sc, L.eNS, 1024⟩
  else .seq (mulC sc ⟨sc, L.eP, 1024⟩ ⟨sc, L.eA, 1024⟩ ⟨sc, 1024 * j, 1024⟩ ⟨sc, L.eNS, 1024⟩)
    (addC sc ⟨sc, L.eU, 1024⟩ ⟨sc, L.eP, 1024⟩)

/-- `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, compressed into `c[32d_u·i : 32d_u·(i + 1)]`. -/
def encRow (sc i : Nat) : Prog isa :=
  seqs ((List.range L.p.k).map (encEntry L sc i)) <|
  .seq (nttInvC sc ⟨sc, L.eU, 1024⟩ ⟨sc, L.eNS, 1024⟩) <| .seq (encCbd L sc (L.p.k + i) L.eE) <|
  .seq (addC sc ⟨sc, L.eU, 1024⟩ ⟨sc, L.eE, 1024⟩)
    (ceK L sc L.p.du ⟨sc, L.eU, 1024⟩ ⟨sc, L.eC + 32 * L.p.du * i, 32 * L.p.du⟩)

/-- `t̂[j] ← ByteDecode₁₂(ek[384j : 384j + 384])`, times `ŷ[j]`, added to `v`
(written to it if `j = 0`). -/
def encTerm (sc j : Nat) : Prog isa :=
  .seq (dec12C sc ⟨sc, L.eEK + 384 * j, 384⟩ ⟨sc, L.eT, 1024⟩) <|
  if j = 0 then mulC sc ⟨sc, L.eU, 1024⟩ ⟨sc, L.eT, 1024⟩ ⟨sc, 0, 1024⟩ ⟨sc, L.eNS, 1024⟩
  else .seq (mulC sc ⟨sc, L.eP, 1024⟩ ⟨sc, L.eT, 1024⟩ ⟨sc, 1024 * j, 1024⟩ ⟨sc, L.eNS, 1024⟩)
    (addC sc ⟨sc, L.eU, 1024⟩ ⟨sc, L.eP, 1024⟩)

/-- `v = NTT⁻¹(t̂ ∘ ŷ) + e₂ + μ`, compressed into `c[32d_u·k : 32(d_u·k + d_v)]`. -/
def encV (sc : Nat) : Prog isa :=
  seqs ((List.range L.p.k).map (encTerm L sc)) <|
  .seq (nttInvC sc ⟨sc, L.eU, 1024⟩ ⟨sc, L.eNS, 1024⟩) <| .seq (encCbd L sc (2 * L.p.k) L.eE) <|
  .seq (addC sc ⟨sc, L.eU, 1024⟩ ⟨sc, L.eE, 1024⟩) <|
  .seq (ddC sc 1 ⟨sc, L.eM, 32⟩ ⟨sc, L.eMU, 1024⟩) <| .seq (addC sc ⟨sc, L.eU, 1024⟩ ⟨sc, L.eMU, 1024⟩)
    (ceK L sc L.p.dv ⟨sc, L.eU, 1024⟩ ⟨sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩)

/-- K-PKE.Encrypt(ek, m, r), with `ek`, `m` and `r` in `scratch`, the ciphertext into it. -/
def encrypt (sc : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm 1), .store (at_ .esi L.eACC) .eax]) <|
  seqs ((List.range L.p.k).map (encYC L sc)) <|
  seqs ((List.range L.p.k).map (encRow L sc)) (encV L sc)

end VG.Impl.MlKem.X86
