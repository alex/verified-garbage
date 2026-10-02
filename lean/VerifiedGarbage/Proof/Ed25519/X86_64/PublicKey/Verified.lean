import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Shared

/-!
# Ed25519 public-key derivation on x86-64: the shared contract

`vg_ed25519_public_key`, made with any implementation `v` of the SHA-512
compression function, is verified against `Spec.Ed25519.publicKeyContract` for
the 72 bytes of stack its frame and calls use.
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

theorem publicKey_ct (v : Compress) :
    ConstantTime isa pkLocal.pre pkLocal.pub (publicKey fld fs v.callee v.suffix) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1) (RelCT.mono (body_ct v) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by simp only [lay, hsp, hdi, hsi, hdx]
  exact ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, lay_ok h₁, push_ctx h₁,
    e ▸ push_ctx h₂, trivial, trivial⟩

theorem implies : pkLocal.Implies (Spec.Ed25519.publicKeyContract X86_64.abi 72) := by
  sig_implies [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig, Spec.Ed25519.scratchWords,
    X86_64.abi, X86_64.argRegs, pkLocal] [Proof.Ed25519.X86_64.baseSatState]
    using Proof.Ed25519.X86_64.baseSatState

theorem publicKey_verified (v : Compress) :
    Verified X86_64.target (publicKey fld fs v.callee v.suffix) (Spec.Ed25519.publicKeyContract X86_64.abi 72) :=
  Verified.of_correct (fun _ h => publicKey_ok v h) (publicKey_ct v) implies

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem publicKey_spSafe (v : Compress) :
    (publicKey fld fs v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  have hu := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe
  have hf := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe
  have hb : (scalarBase_precomputed fld).all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by fld_lit_decide)
  have hi : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all (fun i => !isa.writesSp i) = true := by
    decide +kernel
  simp only [publicKey, pkBody, pkHash, callWith, Code.all, hu, hf, hb, hi, Bool.and_true, Bool.true_and]
  decide

end VG.Proof.Ed25519.X86_64.PublicKey
