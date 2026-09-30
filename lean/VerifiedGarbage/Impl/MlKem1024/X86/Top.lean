import VerifiedGarbage.Impl.MlKem.X86.Top
import VerifiedGarbage.Impl.MlKem1024.X86.Compress

/-!
# ML-KEM-1024 on x86 (32-bit): calls of the compression to 5 and 11 bits

The building blocks of the top-level functions are those of ML-KEM-768
(`Impl/MlKem/X86/Top.lean`), and these calls of
`vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`, with
their arguments set as `ceC` and `ddC` set those of `vg_mlkem_compress_encode`
and `vg_mlkem_decode_decompress`.
-/

namespace VG.Impl.MlKem1024.X86

open VG.X86 VG.Impl.MlKem.X86

/-- `o ← ByteEncode_d(Compress_d(f))` (`vg_mlkem1024_compress_encode`). -/
def ceC1024 (sc d : Nat) (f o : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax f ++ ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo sc .edx o ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr)))
    (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem1024_compress_encode" compressEncode)

/-- `f ← Decompress_d(ByteDecode_d(b))` (`vg_mlkem1024_decode_decompress`). -/
def ddC1024 (sc d : Nat) (b f : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax b ++ ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))),
      .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo sc .edi f))
    (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem1024_decode_decompress" decodeDecompress)

end VG.Impl.MlKem1024.X86
