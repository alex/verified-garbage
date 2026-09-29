import VerifiedGarbage.Impl.MlKem1024.AArch64.Kem
import VerifiedGarbage.Impl.MlKem.AArch64.Decaps

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decaps`

`decaps(dk = x0, ct = x1, key = x2, scratch = x3) -> x0`:
`Decaps_internal(dk, c)` (FIPS 203 Algorithms 18, 15 and 14) of ML-KEM-1024,
as ML-KEM-768's (`Impl/MlKem/AArch64/Decaps.lean`). We keep `dk`, `ct`, `key`
and `scratch` in `x25`–`x28`, and the AND of `sample_ntt`'s results in `x24`.

1. `m' = K-PKE.Decrypt(dk_PKE, c)` into `scratch` (`deM`): `u'[i]` and its
   NTT into `ŷ[i]`'s buffer, `ŝ[i]` decoded from `dk`, `v'`, and `m'`.
2. `(K', r') = G(m' ‖ h)`, with `h` in `dk`, into `scratch`; `ρ` (bytes
   3072–3103 of `dk`) into `scratch`.
3. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the sixteen `(i, j)`.
4. `c' = K-PKE.Encrypt(ek_PKE, m', r')` into `scratch` (`encryptC`), with
   `ek_PKE` in `dk`; `K̄ = J(z ‖ c)`, with `z` in `dk`, into `scratch`.
5. `c = c'` without branching: the OR of the bytes of `c ⊕ c'` (`deCmp`),
   a mask of ones if it is 0, and `K'` or `K̄` into `key` through the mask
   (`deSel`).

Returns 1 if every `SampleNTT` finished within 280 iterations, and 0 if not
(when `key` is then unspecified). Only the calls of `sample_ntt` depend on
`ρ` (which the contract declares that the function may leak); every other
address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem1024.AArch64

open VG.AArch64 KEM
open VG.Impl.MlKem.AArch64 (hash copy32 ptrTo deCmpBody)

/-- `û'[i] = NTT(Decompress₁₁(ByteDecode₁₁(c[352i : 352i + 352])))`, into `ŷ[i]`'s buffer. -/
def deU (i : Nat) : Prog isa := .seq (ddWAt .x26 (352 * i) 11 (yOff i)) (nttAt (yOff i))

/-- `m' = ByteEncode₁(Compress₁(v' - NTT⁻¹(ŝ[0] û'[0] + ⋯ + ŝ[3] û'[3])))`, into `MB`. -/
def deM : Prog isa :=
  .seq (deU 0) <| .seq (deU 1) <| .seq (deU 2) <| .seq (deU 3) <|
  .seq (dec12At .x25 0 TH) <| .seq (mulAt TP TH (yOff 0)) <|
  .seq (dec12At .x25 384 TH) <| .seq (mulAt PP TH (yOff 1)) <| .seq (addAt TP PP) <|
  .seq (dec12At .x25 768 TH) <| .seq (mulAt PP TH (yOff 2)) <| .seq (addAt TP PP) <|
  .seq (dec12At .x25 1152 TH) <| .seq (mulAt PP TH (yOff 3)) <| .seq (addAt TP PP) <|
  .seq (nttInvAt TP) <| .seq (ddWAt .x26 1408 5 EP) <| .seq (subAt EP TP) (ceAt EP 1 .x28 MB)

/-- The prologue, `m'`, `G(m' ‖ h)` and `ρ`. -/
def deA : Prog isa :=
  .seq (.block (kemPrologue 3 [0, 1, 2, 3])) <| .seq deM <|
  .seq (hash .x28 ST WK 72 6 [⟨.x28, MB, 32⟩, ⟨.x25, 3104, 32⟩] [⟨.x28, KP, 32⟩, ⟨.x28, RB, 32⟩])
    (.block (copy32 .x25 3072 .x28 SB))

/-- The OR of the bytes of `c ⊕ c'` into `x10`, then a mask in `x10`: all
ones if it is 0 (`c = c'`), and 0 otherwise. -/
def deCmp : Prog isa :=
  .seq (.block (ptrTo .x0 .x26 0 ++ ptrTo .x1 .x28 CB ++
      ([.movz .x .x2 1568 0, .movz .x .x10 0 0] : List Instr))) <|
  .seq (.loop (.block deCmpBody) (.nonzero .x .x2))
    (.block [.subImm .x .x10 .x10 1, .lsr .x .x10 .x10 63, .movz .x .x11 0 0, .sub .x .x10 .x11 .x10])

/-- Eight bytes of `K'` or `K̄` into `key`, through the mask in `x10`. -/
def deSelWord (k : Nat) : List Instr :=
  [.ldr .x .x12 .x28 (KP + 8 * k), .ldr .x .x13 .x28 (JB + 8 * k), .logic .eor .x .x12 .x12 .x13,
    .logic .and .x .x12 .x12 .x10, .logic .eor .x .x12 .x12 .x13, .str .x .x12 .x27 (8 * k)]

/-- `K'` or `K̄` into `key`. -/
def deSel : List Instr := (List.range 4).flatMap deSelWord

/-- `c'`, `K̄`, the comparison, the key and the epilogue. -/
def deC : Prog isa :=
  .seq (encryptC .x25 1536 .x28 MB .x28 CB) <|
  .seq (hash .x28 ST WK 136 0x1f [⟨.x25, 3136, 32⟩, ⟨.x26, 0, 1568⟩] [⟨.x28, JB, 32⟩]) <|
  .seq deCmp (.block (deSel ++ kemEpilogue))

def decaps : Prog isa := .seq deA (.seq kemMatrix deC)

end VG.Impl.MlKem1024.AArch64
