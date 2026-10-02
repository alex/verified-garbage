import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode

/-!
# ML-DSA on AArch64: the encodings as literals

The code of the packing functions, built by functions of the width, as
literals (`materialize_code`, `Proof/Framework/Lit.lean`): the kernel checks
each literal once here, and then evaluates it, rather than building the
instructions again, in every check that evaluates the code (constant time,
`spSafe`, properties of every instruction).
-/

namespace VG

materialize_code Impl.MlDsa.AArch64.Pack.simpleBitPack
materialize_code Impl.MlDsa.AArch64.Pack.bitPack
materialize_code Impl.MlDsa.AArch64.Pack.bitUnpack
materialize_code Impl.MlDsa.AArch64.Pack.unpackT1

end VG
