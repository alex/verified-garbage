import VerifiedGarbage.Impl.MlKem.AArch64.Kem

/-!
# ML-KEM on AArch64: `vg_mlkem768_decaps` and `vg_mlkem1024_decaps`

`(L.decapsWith c)(dk = x0, ct = x1, key = x2, scratch = x3) -> x0`:
`Decaps_internal(dk, c)` (FIPS 203 Algorithms 18, 15 and 14) of the parameter set `L`, as calls of
the verified primitives and Keccak functions. We keep `dk`, `ct`, `key` and
`scratch` in `x25`–`x28`, and the AND of `sample_ntt`'s results in `x24`.

1. `m' = K-PKE.Decrypt(dk_PKE, c)` into `scratch` (`deM`): `u'[i]` and its
   NTT into `ŷ[i]`'s buffer, `ŝ[i]` decoded from `dk`, `v'`, and `m'`.
2. `(K', r') = G(m' ‖ h)`, with `h` in `dk`, into `scratch`; `ρ` (bytes
   `768k` to `768k + 31` of `dk`) into `scratch`.
3. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the `k²` entries `(i, j)`.
4. `c' = K-PKE.Encrypt(ek_PKE, m', r')` into `scratch` (`L.encryptCWith c`), with
   `ek_PKE` in `dk`; `K̄ = J(z ‖ c)`, with `z` in `dk`, into `scratch`.
5. `c = c'` without branching: the OR of the bytes of `c ⊕ c'` (`deCmp`),
   a mask of ones if it is 0, and `K'` or `K̄` into `key` through the mask
   (`deSel`).

Returns 1 if every `SampleNTT` finished within 280 iterations, and 0 if not
(when `key` is then unspecified). Only the calls of `sample_ntt` depend on
`ρ` (which the contract declares that the function may leak); every other
address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64 KEM

/-- One byte of `c ⊕ c'` ORed into `x10`. -/
def deCmpBody : List Instr :=
  [.ldrb .x9 .x0 0, .ldrb .x11 .x1 0, .logic .eor .x .x9 .x9 .x11, .logic .orr .x .x10 .x10 .x9,
    .addImm .x .x0 .x0 1, .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]

/-- Eight bytes of `K'` or `K̄` into `key`, through the mask in `x10`. -/
def deSelWord (k : Nat) : List Instr :=
  [.ldr .x .x12 .x28 (KP + 8 * k), .ldr .x .x13 .x28 (JB + 8 * k), .logic .eor .x .x12 .x12 .x13,
    .logic .and .x .x12 .x12 .x10, .logic .eor .x .x12 .x12 .x13, .str .x .x12 .x27 (8 * k)]

/-- `K'` or `K̄` into `key`. -/
def deSel : List Instr := (List.range 4).flatMap deSelWord

namespace KemLay

variable (L : KemLay)

/-- `û'[i] = NTT(Decompress_{d_u}(ByteDecode_{d_u}(c[32 d_u i : 32 d_u (i + 1)])))`, into `ŷ[i]`'s
buffer. -/
def deU (i : Nat) : Prog isa := .seq (L.ddLAt .x26 (32 * L.du * i) L.du (yOff L i)) (nttAt (yOff L i))

/-- `m' = ByteEncode₁(Compress₁(v' - NTT⁻¹(ŝ[0] û'[0] + ⋯ + ŝ[k - 1] û'[k - 1])))`, into `MB`. -/
def deM : Prog isa :=
  seqs ((List.range L.k).map L.deU ++
    dotSteps (TP L) (PP L) (fun j h => [dec12At .x25 (384 * j) (TH L), mulAt h (TH L) (yOff L j)]) L.k ++
    [nttInvAt (TP L), L.ddLAt .x26 (32 * L.du * L.k) L.dv (EP L), subAt (EP L) (TP L), ceAt (EP L) 1 .x28 MB])

/-- The prologue, `m'`, `G(m' ‖ h)` and `ρ`. -/
def deAWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block (L.kemPrologue 3 [0, 1, 2, 3])) <| .seq L.deM <|
  .seq (hashWith c .x28 ST WK 72 6 [⟨.x28, MB, 32⟩, ⟨.x25, 768 * L.k + 32, 32⟩]
      [⟨.x28, KP, 32⟩, ⟨.x28, RB, 32⟩])
    (.block (copy32 .x25 (768 * L.k) .x28 SB))

/-- The OR of the bytes of `c ⊕ c'` into `x10`, then a mask in `x10`: all
ones if it is 0 (`c = c'`), and 0 otherwise. -/
def deCmp : Prog isa :=
  .seq (.block (ptrTo .x0 .x26 0 ++ ptrTo .x1 .x28 (CB L) ++
      ([.movz .x .x2 (BitVec.ofNat 16 L.ctLen) 0, .movz .x .x10 0 0] : List Instr))) <|
  .seq (.loop (.block deCmpBody) (.nonzero .x .x2))
    (.block [.subImm .x .x10 .x10 1, .lsr .x .x10 .x10 63, .movz .x .x11 0 0, .sub .x .x10 .x11 .x10])

/-- `c'`, `K̄`, the comparison, the key and the epilogue. -/
def deCWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (L.encryptCWith c .x25 (384 * L.k) .x28 MB .x28 (CB L)) <|
  .seq (hashWith c .x28 ST WK 136 0x1f [⟨.x25, 768 * L.k + 64, 32⟩, ⟨.x26, 0, L.ctLen⟩] [⟨.x28, JB, 32⟩]) <|
  .seq L.deCmp (.block (deSel ++ L.kemEpilogue))

def decapsWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (L.deAWith c) (.seq (L.kemMatrixWith c) (L.deCWith c))

end KemLay

abbrev deAWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay768.deAWith c
abbrev deCWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay768.deCWith c
abbrev decapsWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := lay768.decapsWith c
abbrev decaps : Prog isa := decapsWith .scalar

end VG.Impl.MlKem.AArch64
