import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Blake2.X86.Blake2s

/-! # BLAKE2s (RFC 7693) on x86 -/

namespace VG.Artifacts.Blake2s.X86

def artifacts : List Artifact := [
  { Spec.Blake2.compressSApi with
    target := X86.target
    doc := Spec.Blake2.compressSApi.doc
    code := Impl.Blake2.X86.CompressS.compress
    contract := Spec.Blake2.compressSContract X86.abi
    verified := Proof.Blake2.X86.S.compress_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.initSApi with
    target := X86.target
    doc := Spec.Blake2.initSApi.doc
    code := Impl.Blake2.X86.Stream.init Spec.Blake2.s
    contract := Spec.Blake2.initSContract X86.abi
    verified := Proof.Blake2.X86.S.init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.updateSApi with
    target := X86.target
    doc := Spec.Blake2.updateSApi.doc
    code := Impl.Blake2.X86.Stream.update 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress
    contract := Spec.Blake2.updateSContract X86.abi 32
    stack := 32
    verified := Proof.Blake2.X86.S.update_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.finalizeSApi with
    target := X86.target
    doc := Spec.Blake2.finalizeSApi.doc
    code := Impl.Blake2.X86.Stream.finalize 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress
    contract := Spec.Blake2.finalizeSContract X86.abi 32
    stack := 32
    verified := Proof.Blake2.X86.S.finalize_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Blake2s.X86
