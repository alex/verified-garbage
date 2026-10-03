import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash

/-!
# AES-GCM on x86-64: the implementations of `vg_ghash`

Untrusted: everything here is checked by Lean. The `GhashImpl`s of
`vg_ghash`, `vg_ghash_pclmul` and `vg_ghash_vpclmul`, from their proofs,
apart from `Callee.lean`: only the variants need them, and their proofs import the
algebra of `Proof/Gcm/Poly.lean`, which the rest of the AES-GCM proofs then
need not import.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

namespace GhashImpl

/-- `vg_ghash`, in the baseline ISA. -/
def scalar : GhashImpl where
  fn := ⟨"vg_ghash", Impl.Gcm.X86_64.ghash⟩
  depth := by lit_decide
  ok := Proof.Gcm.X86_64.ghash_correct
  ct := Proof.Gcm.X86_64.ghash_ct
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []

/-- `vg_ghash_pclmul`. -/
def pclmul : GhashImpl where
  fn := ⟨"vg_ghash_pclmul", Impl.Gcm.X86_64.Pclmul.ghash⟩
  depth := by lit_decide
  ok := Proof.Gcm.X86_64.Pclmul.ghash_correct
  ct := Proof.Gcm.X86_64.Pclmul.ghash_ct
  nosp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_pclmul"
  features := ["pclmulqdq", "ssse3"]

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
