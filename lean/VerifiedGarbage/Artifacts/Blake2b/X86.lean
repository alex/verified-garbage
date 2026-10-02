import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Blake2.X86.Blake2b

/-! # BLAKE2b (RFC 7693) on x86 -/

namespace VG.Artifacts.Blake2b.X86

def artifacts : List Artifact := [
  { Spec.Blake2.compressBApi with
    target := X86.target
    doc := Spec.Blake2.compressBApi.doc
    code := Impl.Blake2.X86.CompressB.compress
    contract := Spec.Blake2.compressBContract X86.abi
    verified := Proof.Blake2.X86.CompressB.compressB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.initBApi with
    target := X86.target
    doc := Spec.Blake2.initBApi.doc
    code := Impl.Blake2.X86.Stream.init Spec.Blake2.b
    contract := Spec.Blake2.initBContract X86.abi
    verified := Proof.Blake2.X86.B.initB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.updateBApi with
    target := X86.target
    doc := Spec.Blake2.updateBApi.doc
    code := Impl.Blake2.X86.Stream.update 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress
    contract := Spec.Blake2.updateBContract X86.abi 32
    stack := 32
    verified := Proof.Blake2.X86.B.updateB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.finalizeBApi with
    target := X86.target
    doc := Spec.Blake2.finalizeBApi.doc
    code := Impl.Blake2.X86.Stream.finalize 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress
    contract := Spec.Blake2.finalizeBContract X86.abi 32
    stack := 32
    verified := Proof.Blake2.X86.B.finalizeB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Blake2b.X86
