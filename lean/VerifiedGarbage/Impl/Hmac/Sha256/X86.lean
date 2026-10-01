import VerifiedGarbage.Impl.Hmac.X86
import VerifiedGarbage.Impl.MdStream.X86

/-! SHA-256's efficient x86 HMAC bodies, generic over compression. -/
namespace VG.Impl.Hmac.Sha256.X86
open VG.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (save restore)
open VG.Impl.Hmac.X86 (h0 keyLoop padLoop opadWord bswapWord copyWord padWords)

def compressBuf (name : String) (code : Prog isa) (b : Reg) : Prog isa :=
  .seq (.block [.mov .eax (.reg b), .alu .add .eax (.imm 32)]) (Impl.MdStream.X86.compressAt name code b .ebp)

def init (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block ([.mov .eax (.mem (at_ .esp 20))] ++ save .eax ++
      [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 8))] ++
      h0 .ebx ++ h0 .esi ++
      [.mov .edi (.mem (at_ .esp 12)), .mov .ecx (.mem (at_ .esp 16)), .mov .edx (.reg .ebx),
       .alu .add .edx (.imm 32), .alu .test .ecx (.reg .ecx)]))
  (.seq (.ite .e (.block []) keyLoop)
  (.seq (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 96), .mov .ecx (.imm 0x36),
      .alu .cmp .edx (.reg .eax)])
  (.seq (.ite .e (.block []) padLoop)
  (.seq (.block ((List.range 16).flatMap opadWord))
  (.seq (compressBuf name code .ebx)
  (.seq (compressBuf name code .esi)
    (.block (.mov .eax (.reg .ebp) :: restore .eax))))))))

def finalizeHash (name : String) (code : Prog isa) : Prog isa :=
  match Impl.MdStream.X86.finalize Impl.Sha256.X86.Stream.params name code with
  | .seq a (.seq b (.seq c _)) => .seq a (.seq b c)
  | p => p

def finalize (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mov .edx (.mem (at_ .esp 24)), .mov .ecx (.mem (at_ .esp 8)), .store (at_ .edx 176) .ecx,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .esp 8) .ecx,
      .mov .ecx (.mem (at_ .esp 16)), .store (at_ .esp 12) .ecx,
      .mov .ecx (.mem (at_ .esp 20)), .store (at_ .esp 16) .ecx, .store (at_ .esp 20) .edx])
  (.seq (finalizeHash name code)
  -- The inner digest into the inner buffer, and the outer hash value into the inner state.
  (.seq (.block ((List.range 8).flatMap (bswapWord .ebx .ebx 0 32) ++ .mov .edx (.mem (at_ .ebp 176)) ::
      (List.range 8).flatMap (copyWord .edx .ebx 0 0) ++ padWords ++
      [.mov .eax (.reg .ebx), .alu .add .eax (.imm 32)]))
  (.seq (Impl.MdStream.X86.compressAt name code .ebx .ebp)
    (.block (.mov .eax (.mem (at_ .ebp 136)) :: (List.range 8).flatMap (bswapWord .ebx .eax 0 0) ++
      .mov .eax (.reg .ebp) :: restore .eax)))))

end VG.Impl.Hmac.Sha256.X86
