import VerifiedGarbage.Impl.MlKem.AArch64.Kem

/-!
# ML-KEM-768 on AArch64: `vg_mlkem768_encaps`

`(encapsWith c)(ek = x0, m = x1, key = x2, ct = x3, scratch = x4) -> x0`:
`Encaps_internal(ek, m)` (FIPS 203 Algorithms 17 and 14), as calls of the
verified primitives and Keccak functions. We keep `ek`, `key`, `ct` and
`scratch` in `x25`–`x28`, and the AND of `sample_ntt`'s results in `x24`.

1. `m` into `scratch`; `H(ek)` into `scratch`, then `(K, r) = G(m ‖ H(ek))`,
   with `K` into `key` and `r` into `scratch`; `ρ` (bytes 1152–1183 of `ek`)
   into `scratch`.
2. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the nine `(i, j)`.
3. `ŷ`, `u` into `ct`, and `v` into `ct` (`(encryptCWith c)`).

Returns 1 if every `SampleNTT` finished within 280 iterations, and 0 if not
(when `key` and `ct` are then unspecified). Only the calls of `sample_ntt`
depend on `ρ` (which the contract declares that the function may leak);
every other address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64 KEM

/-- The prologue, `m`, `H(ek)`, `G(m ‖ H(ek))` and `ρ`. -/
def enAWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block (kemPrologue 4 [0, 2, 3, 4] ++ copy32 .x1 0 .x28 MB)) <|
  .seq (hashWith c .x28 ST WK 136 6 [⟨.x25, 0, 1184⟩] [⟨.x28, HB, 32⟩]) <|
  .seq (hashWith c .x28 ST WK 72 6 [⟨.x28, MB, 32⟩, ⟨.x28, HB, 32⟩] [⟨.x26, 0, 32⟩, ⟨.x28, RB, 32⟩])
    (.block (copy32 .x25 1152 .x28 SB))

/-- `ŷ`, `u`, `v` and the epilogue. -/
def enCWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := .seq ((encryptCWith c) .x25 0 .x28 MB .x27 0) (.block kemEpilogue)

def encapsWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := .seq (enAWith c) (.seq (kemMatrixWith c) (enCWith c))

def enA := enAWith .scalar
def enC := enCWith .scalar
def encaps := encapsWith .scalar

end VG.Impl.MlKem.AArch64
