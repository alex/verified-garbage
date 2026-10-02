import VerifiedGarbage.Proof.X25519.AArch64.Word.Top
import VerifiedGarbage.Proof.X25519.AArch64.Word.Lit
import VerifiedGarbage.Proof.X25519.AArch64.Verified

/-! Correctness, constant time, and the original shared contract. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64

theorem x25519_ct : ConstantTime isa localContract.pre localContract.pub
    Impl.X25519.AArch64.Word.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ hp => VG.Proof.X25519.AArch64.agree₀ hp) (by taint_decide)

theorem x25519_verified : Verified AArch64.target Impl.X25519.AArch64.Word.x25519
    (Spec.X25519.x25519Contract AArch64.abi) :=
  Verified.of_correct x25519_ok x25519_ct (by
    sig_implies [Spec.X25519.x25519Contract,Spec.X25519.x25519Sig,AArch64.abi,AArch64.argRegs,
      localContract,Proof.X25519.x25519AArch64] [VG.Proof.X25519.AArch64.sat]
      using VG.Proof.X25519.AArch64.sat)
end VG.Proof.X25519.AArch64.Word
