import VerifiedGarbage.Impl.Pbkdf2.X86
import VerifiedGarbage.Impl.MdStream.X86

/-! PBKDF2-SHA-256's two-compression iteration, generic over compression. -/
namespace VG.Impl.Pbkdf2.Sha256.X86
open VG.X86
open VG.Impl.Pbkdf2.X86 (load atBlock digest xorW prologue epilogue)

def body (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (load 0 ++ atBlock))
  (.seq (Impl.MdStream.X86.compressAt name code .ebx .ebp)
  (.seq (.block (digest ++ load 96 ++ atBlock))
  (.seq (Impl.MdStream.X86.compressAt name code .ebx .ebp)
    (.block (digest ++ (List.range 8).flatMap xorW ++ [.alu .sub .edi (.imm 1)])))))

def iterate (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block prologue)
  (.seq (.ite .e (.block []) (.loop (body name code) .ne)) (.block epilogue))

end VG.Impl.Pbkdf2.Sha256.X86
