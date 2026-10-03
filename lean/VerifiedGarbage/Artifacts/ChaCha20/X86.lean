import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.ChaCha20.X86.Xor
import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.ChaCha20.X86.Stream.ApplyCT

/-! # The ChaCha20 block function (RFC 8439) on x86 -/

namespace VG.Artifacts.ChaCha20.X86

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := X86.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.X86.block
    contract := Spec.ChaCha20.blockContract X86.abi
    verified := Proof.ChaCha20.X86.block_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20.xorApi with
    target := X86.target
    doc := Spec.ChaCha20.xorApi.doc (notes := ["Calls `vg_chacha20_block` for each 64 bytes."])
    code := Impl.ChaCha20.X86.Xor.xor
    contract := Spec.ChaCha20.xorContract X86.abi 12
    stack := 12
    verified := Proof.ChaCha20.X86.Xor.xor_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20.initApi with
    target := X86.target
    doc := Spec.ChaCha20.initApi.doc
    code := Impl.ChaCha20.X86.Stream.init
    contract := Spec.ChaCha20.initContract X86.abi
    verified := Proof.ChaCha20.X86.Stream.init_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.ChaCha20.setNonceApi with
    target := X86.target
    doc := Spec.ChaCha20.setNonceApi.doc
    code := Impl.ChaCha20.X86.Stream.setNonce
    contract := Spec.ChaCha20.setNonceContract X86.abi
    verified := Proof.ChaCha20.X86.Stream.setNonce_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.ChaCha20.applyApi with
    target := X86.target
    doc := Spec.ChaCha20.applyApi.doc
    code := Impl.ChaCha20.X86.Stream.apply
    contract := Spec.ChaCha20.applyContract X86.abi 32
    stack := 32
    verified := Proof.ChaCha20.X86.Stream.apply_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.ChaCha20.X86
