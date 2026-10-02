import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode

/-!
# ML-DSA on AArch64: the encodings as literals

The code of the packing functions, built by functions of the width, as
literals (`materialize_code`, `Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.MlDsa.AArch64.Pack.simpleBitPack
materialize_code Impl.MlDsa.AArch64.Pack.bitPack
materialize_code Impl.MlDsa.AArch64.Pack.bitUnpack
materialize_code Impl.MlDsa.AArch64.Pack.unpackT1

end VG
