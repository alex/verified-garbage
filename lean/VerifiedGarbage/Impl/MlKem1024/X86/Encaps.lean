import VerifiedGarbage.Impl.MlKem1024.X86.Encrypt

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_encaps`

`encaps(ek, m, key, ct, scratch) -> eax`: `ML-KEM.Encaps_internal(ek, m)`
(Algorithm 17), as `vg_mlkem768_encaps` (`Impl/MlKem/X86/Encaps.lean`). `ek`
and `m` are copied into `scratch` (argument 4, in `esi`), `H(ek)` hashed to
`scratch + en4H`, `(K, r) = G(m ‖ H(ek))` to `e4KR`, the ciphertext computed
by `encrypt4` (`Encrypt.lean`), and `K` and the ciphertext copied into `key`
and `ct`; `e4ACC` is returned.
-/

namespace VG.Impl.MlKem1024.X86

open VG.X86 VG.Impl.MlKem.X86

/-- `H(ek)`. -/
def en4H : Nat := 17528

def encaps4Body : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 36))]) <|
  .seq (copyW 4 ⟨0, 0, 1568⟩ ⟨4, e4EK, 1568⟩ 392) <|
  .seq (copyW 4 ⟨1, 0, 32⟩ ⟨4, e4M, 32⟩ 8) <|
  .seq (hash1 4 e4ST e4WK 136 6 ⟨4, e4EK, 1568⟩ ⟨4, en4H, 32⟩) <|
  .seq (hash2 4 e4ST e4WK 72 6 ⟨4, e4M, 32⟩ ⟨4, en4H, 32⟩ ⟨4, e4KR, 64⟩) <|
  .seq (encrypt4 4) <|
  .seq (copyW 4 ⟨4, e4KR, 32⟩ ⟨2, 0, 32⟩ 8) <|
  .seq (copyW 4 ⟨4, e4C, 1568⟩ ⟨3, 0, 1568⟩ 392) (.block [.mov .eax (.mem (at_ .esi e4ACC))])

def encaps : Prog isa := leaf encaps4Body

end VG.Impl.MlKem1024.X86
