import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash

/-!
# AES-GCM on AArch64: `vg_ghash_aes`

Untrusted: everything here is checked by Lean. The `GhashImpl` of
`vg_ghash_aes`, from its proof, apart from `Callee.lean`: only the variants
need it, and its proof imports the algebra of `Proof/Gcm/Poly.lean`, which
the rest of the AES-GCM proofs then need not import.
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64

namespace GhashImpl

/-- `vg_ghash_aes`, with PMULL (which Rust's `aes` feature stands for, with
the AES instructions). -/
def aes : GhashImpl where
  fn := ⟨"vg_ghash_aes", Impl.Gcm.AArch64.Pmull.ghash⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghash_correct
  ct := Proof.Gcm.AArch64.Pmull.ghash_ct
  keepsV := by decide +kernel
  suffix := "_aes"
  features := ["aes"]

end GhashImpl

end VG.Proof.AesGcm.AArch64
