import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn

/-!
# ML-DSA (FIPS 204) on x86-64: signing messages

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which call
`vg_mldsa*_sign` with an implementation `v` of the polynomial arithmetic
(`Variants/MlDsaArith/X86_64/`), are emitted once for each implementation,
named with its suffix (e.g. `vg_mldsa44_sign_message_avx2`), and need its CPU
features. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Generic.MlDsaArith.X86_64.MlDsaSignMessage

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)
open VG.Proof.MlDsa.X86_64.Message (signFn signMessage_verified signMessage_spSafe)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function keeps its arguments in a frame of 72 bytes on the stack, and its calls use the 32 \
    bytes of stack below the frame. It computes the message representative with the SHAKE256 sponge \
    (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in the last 1 KiB of `scratch`, and \
    calls the signing function on it, which uses the rest of `scratch`."]

def artifacts (v : ArithImpl) : List Artifact := [
  { Spec.MlDsa.signMessage44Api with
    name := Spec.MlDsa.signMessage44Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.signMessage44Api.doc (notes := notes)
    code := Impl.MlDsa.X86_64.Message.signMessage (Spec.MlDsa.sign44Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.signMessageContract Spec.MlDsa.mlDsa44 X86_64.abi 104
    stack := 104
    verified := signMessage_verified (signFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) },
  { Spec.MlDsa.signMessage65Api with
    name := Spec.MlDsa.signMessage65Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.signMessage65Api.doc (notes := notes)
    code := Impl.MlDsa.X86_64.Message.signMessage (Spec.MlDsa.sign65Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.signMessageContract Spec.MlDsa.mlDsa65 X86_64.abi 104
    stack := 104
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) },
  { Spec.MlDsa.signMessage87Api with
    name := Spec.MlDsa.signMessage87Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.signMessage87Api.doc (notes := notes)
    code := Impl.MlDsa.X86_64.Message.signMessage (Spec.MlDsa.sign87Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.signMessageContract Spec.MlDsa.mlDsa87 X86_64.abi 104
    stack := 104
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaSignMessage
