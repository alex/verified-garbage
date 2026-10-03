import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Ghash

/-!
# AES-GCM on x86: `vg_ghash_pclmul`

Untrusted: everything here is checked by Lean. The `GhashImpl` of
`vg_ghash_pclmul`, from its proof, apart from `Callee.lean`: only the
variants need it, and its proof imports the algebra of
`Proof/Gcm/Poly.lean`, which the rest of the AES-GCM proofs then need not
import.
-/

namespace VG.Proof.AesGcm.X86

open VG VG.X86

namespace GhashImpl

/-- `vg_ghash_pclmul`. -/
def pclmul : GhashImpl where
  fn := ⟨"vg_ghash_pclmul", Impl.Gcm.X86.Pclmul.ghash⟩
  stack := by lit_decide
  ok := Proof.Gcm.X86.Pclmul.ghash_correct
  ct := Proof.Gcm.X86.Pclmul.ghash_ct
  nosp := NoSp.of_all (by lit_decide)
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_pclmul"
  features := ["pclmulqdq", "ssse3"]

end GhashImpl

end VG.Proof.AesGcm.X86
