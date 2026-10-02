import VerifiedGarbage.Impl.MlKem.X86.Encrypt

/-!
# ML-KEM on x86 (32-bit): encapsulation

`encaps(ek, m, key, ct, scratch) -> eax`: `ML-KEM.Encaps_internal(ek, m)`
(Algorithm 17). `ek` and `m` are copied into `scratch` (argument 4, in
`esi`), `H(ek)` hashed to `scratch + eH`, `(K, r) = G(m ‖ H(ek))` to `eKR`,
the ciphertext computed by `encrypt` (`Encrypt.lean`), and `K` and the
ciphertext copied into `key` and `ct`; `eACC` is returned.
`vg_mlkem768_encaps` is `encaps` (`L768`).
-/

namespace VG.Impl.MlKem.X86

open VG.X86

variable (L : KemLay)

def encapsBody : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 36))]) <|
  .seq (copyW 4 ⟨0, 0, L.p.ekLen⟩ ⟨4, L.eEK, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
  .seq (copyW 4 ⟨1, 0, 32⟩ ⟨4, L.eM, 32⟩ 8) <|
  .seq (hash1 4 L.eST L.eWK 136 6 ⟨4, L.eEK, L.p.ekLen⟩ ⟨4, L.eH, 32⟩) <|
  .seq (hash2 4 L.eST L.eWK 72 6 ⟨4, L.eM, 32⟩ ⟨4, L.eH, 32⟩ ⟨4, L.eKR, 64⟩) <|
  .seq (encrypt L 4) <|
  .seq (copyW 4 ⟨4, L.eKR, 32⟩ ⟨2, 0, 32⟩ 8) <|
  .seq (copyW 4 ⟨4, L.eC, L.p.ctLen⟩ ⟨3, 0, L.p.ctLen⟩ (L.p.ctLen / 4))
    (.block [.mov .eax (.mem (at_ .esi L.eACC))])

/-- `vg_mlkem768_encaps`. -/
def encaps : Prog isa := leaf (encapsBody L768)

end VG.Impl.MlKem.X86
