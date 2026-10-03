import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash

/-!
# AES-GCM on x86-64: `vg_ghash_vpclmul`

Untrusted: everything here is checked by Lean. The `GhashImpl` of
`vg_ghash_vpclmul`, from its proof, apart from `Callee.lean`: only the
variants need it, and its proof imports the algebra of
`Proof/Gcm/Poly.lean`, which the rest of the AES-GCM proofs then need not
import. The variants that call it, or `vg_aes_ctr32_vaes`, import this
module for every implementation of `vg_ghash` they use.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

namespace GhashImpl

/-- `vg_ghash_vpclmul`. -/
def vpclmul : GhashImpl where
  fn := ⟨"vg_ghash_vpclmul", Impl.Gcm.X86_64.Vpclmul.ghash⟩
  depth := by lit_decide
  ok := Proof.Gcm.X86_64.Vpclmul.ghash_correct
  ct := Proof.Gcm.X86_64.Vpclmul.ghash_ct
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_vpclmul"
  features := ["avx", "avx2", "pclmulqdq", "ssse3", "vpclmulqdq"]

end GhashImpl

end VG.Proof.AesGcm.X86_64
