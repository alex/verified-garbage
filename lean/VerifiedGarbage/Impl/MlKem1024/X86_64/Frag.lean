import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Impl.MlKem1024.X86_64.Compress

/-!
# ML-KEM-1024 on x86-64: the pieces of the top-level functions

`vg_mlkem1024_keygen`, `vg_mlkem1024_encaps` and `vg_mlkem1024_decaps` are
built as those of ML-KEM-768 (`Impl/MlKem/X86_64/Frag.lean`, whose pieces
and layout of `scratch` they share), with `k = 4`: the 16 entries of `Â`
are polynomials 17–32 of the working space (`Â[i, j]` is polynomial
`17 + 4i + j`), after the accumulator (polynomial 15) and the products
(polynomial 16), and the ciphertext of the re-encryption (1568 bytes) is in
polynomials 33 and 34. Sums of products have four terms, and the
compression to 11 and 5 bits calls `vg_mlkem1024_compress_encode` and
`vg_mlkem1024_decode_decompress`.
-/

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

/-- `Â[i, j]`: polynomial `17 + 4i + j`. -/
abbrev aS4 (i j : Nat) : Ptr := pS (17 + 4 * i + j)

/-- The ciphertext of the re-encryption (1568 bytes, in polynomials 33 and 34). -/
def oCT4 : Nat := oP 33

/-- `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)`, with `ρ` at `SB`. -/
def sampleIJ4 (i j : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) (sampleAt (aS4 i j))

/-- The sixteen entries of `Â`, row by row (entry `e = 4i + j`). -/
def samples4 : Prog isa := seqR (fun e => sampleIJ4 (e / 4) (e % 4)) 0 16

/-- `f[0] ×_T g[0] + ⋯ + f[3] ×_T g[3]` to polynomial 15 (with 16 for the products). -/
def dot4At (f g : Nat → Ptr) : Prog isa :=
  .seq (dotAt f g) (.seq (mulAt (pS 16) (f 3) (g 3)) (addAt (pS 15) (pS 16)))

def ce4At (f : Ptr) (d : Nat) (out : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 d))] ++ lea .rdx out ++
      [.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * d)))]))
    (.call "vg_mlkem1024_compress_encode" compressEncode1024)

def dd4At (b : Ptr) (d : Nat) (f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi b ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * d))), .mov32 .rdx (.imm (BitVec.ofNat 32 d))] ++
      lea .rcx f))
    (.call "vg_mlkem1024_decode_decompress" decodeDecompress1024)

end VG.Impl.MlKem1024.X86_64
