import VerifiedGarbage.Impl.MlKem.X86.Encrypt

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_encaps`

`encaps(ek, m, key, ct, scratch) -> eax`: `ML-KEM.Encaps_internal(ek, m)`
(Algorithm 17). `ek` and `m` are copied into `scratch` (argument 4, in
`esi`), `H(ek)` hashed to `scratch + enH`, `(K, r) = G(m ‖ H(ek))` to `eKR`,
the ciphertext computed by `encrypt` (`Encrypt.lean`), and `K` and the
ciphertext copied into `key` and `ct`; `eACC` is returned.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `H(ek)`. -/
def enH : Nat := 15640

def encapsBody : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 36))]) <|
  .seq (copyW 4 ⟨0, 0, 1184⟩ ⟨4, eEK, 1184⟩ 296) <|
  .seq (copyW 4 ⟨1, 0, 32⟩ ⟨4, eM, 32⟩ 8) <|
  .seq (hash1 4 eST eWK 136 6 ⟨4, eEK, 1184⟩ ⟨4, enH, 32⟩) <|
  .seq (hash2 4 eST eWK 72 6 ⟨4, eM, 32⟩ ⟨4, enH, 32⟩ ⟨4, eKR, 64⟩) <|
  .seq (encrypt 4) <|
  .seq (copyW 4 ⟨4, eKR, 32⟩ ⟨2, 0, 32⟩ 8) <|
  .seq (copyW 4 ⟨4, eC, 1088⟩ ⟨3, 0, 1088⟩ 272) (.block [.mov .eax (.mem (at_ .esi eACC))])

def encaps : Prog isa := leaf encapsBody

end VG.Impl.MlKem.X86
