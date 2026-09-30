import VerifiedGarbage.Impl.MlKem1024.AArch64.Kem

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_encaps`

`encaps(ek = x0, m = x1, key = x2, ct = x3, scratch = x4) -> x0`:
`Encaps_internal(ek, m)` (FIPS 203 Algorithms 17 and 14) of ML-KEM-1024, as
ML-KEM-768's (`Impl/MlKem/AArch64/Encaps.lean`). We keep `ek`, `key`, `ct`
and `scratch` in `x25`–`x28`, and the AND of `sample_ntt`'s results in `x24`.

1. `m` into `scratch`; `H(ek)` into `scratch`, then `(K, r) = G(m ‖ H(ek))`,
   with `K` into `key` and `r` into `scratch`; `ρ` (bytes 1536–1567 of `ek`)
   into `scratch`.
2. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the sixteen `(i, j)`.
3. `ŷ`, `u` into `ct`, and `v` into `ct` (`encryptC`).

Returns 1 if every `SampleNTT` finished within 280 iterations, and 0 if not
(when `key` and `ct` are then unspecified). Only the calls of `sample_ntt`
depend on `ρ` (which the contract declares that the function may leak);
every other address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64 KEM
open VG.Impl.MlKem.AArch64 (hash copy32)

/-- The prologue, `m`, `H(ek)`, `G(m ‖ H(ek))` and `ρ`. -/
def enA : Prog isa :=
  .seq (.block (kemPrologue 4 [0, 2, 3, 4] ++ copy32 .x1 0 .x28 MB)) <|
  .seq (hash .x28 ST WK 136 6 [⟨.x25, 0, 1568⟩] [⟨.x28, HB, 32⟩]) <|
  .seq (hash .x28 ST WK 72 6 [⟨.x28, MB, 32⟩, ⟨.x28, HB, 32⟩] [⟨.x26, 0, 32⟩, ⟨.x28, RB, 32⟩])
    (.block (copy32 .x25 1536 .x28 SB))

/-- `ŷ`, `u`, `v` and the epilogue. -/
def enC : Prog isa := .seq (encryptC .x25 0 .x28 MB .x27 0) (.block kemEpilogue)

def encaps : Prog isa := .seq enA (.seq kemMatrix enC)

end VG.Impl.MlKem1024.AArch64
