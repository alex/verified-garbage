import VerifiedGarbage.Proof.Aes.X86.Variant
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit

namespace VG.Impl.Aes.X86
materialize_code ctr32
materialize_code expandKey
end VG.Impl.Aes.X86

namespace VG.Proof.Aes.X86.Ctr32Impl
open VG.X86

def scalar : Ctr32Impl where
  callee := .scalar
  depth := by lit_decide
  stack := by lit_decide
  ok := ctr32_correct
  ct := ctr32_ct
  nosp := NoSp.of_all (by lit_decide)
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []
  expand := .scalar
  expandDepth := by lit_decide
  expandStack := by lit_decide
  expandOk := expandKey_correct
  expandCt := expandKey_ct
  expandNosp := NoSp.of_all (by lit_decide)
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)

def aesni : Ctr32Impl where
  callee := .aesni
  depth := by lit_decide
  stack := by lit_decide
  ok := AesNi.ctr32_correct
  ct := AesNi.ctr32_ct
  nosp := NoSp.of_all (by lit_decide)
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_aesni"
  features := ["aes"]
  expand := .aesni
  expandDepth := by lit_decide
  expandStack := by lit_decide
  expandOk := AesNi.expandKey_correct ⟨AesNi.expand128_ok, AesNi.expand192_ok, AesNi.expand256_ok⟩
  expandCt := AesNi.expandKey_ct
  expandNosp := NoSp.of_all (by lit_decide)
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)

end VG.Proof.Aes.X86.Ctr32Impl
