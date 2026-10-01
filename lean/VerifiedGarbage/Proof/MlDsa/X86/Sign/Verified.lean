import VerifiedGarbage.Proof.MlDsa.X86.Sign.Top
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inst

/-!
# ML-DSA signing on x86 (32-bit): verified

Untrusted: everything here is checked by Lean. `vg_mldsa{44,65,87}_sign`
(`sign prims p`) with the x86 primitives, verified against `signContract`
(`verified`, with `prims_ok`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlDsa.X86.Sign
open VG.Spec.MlDsa

theorem sign44_verified : Verified X86.target (sign prims mlDsa44) (signContract mlDsa44 X86.abi 96) :=
  verified prims_ok (.inl rfl) (NoSp.of_all (by decide +kernel))

theorem sign65_verified : Verified X86.target (sign prims mlDsa65) (signContract mlDsa65 X86.abi 96) :=
  verified prims_ok (.inr (.inl rfl)) (NoSp.of_all (by decide +kernel))

theorem sign87_verified : Verified X86.target (sign prims mlDsa87) (signContract mlDsa87 X86.abi 96) :=
  verified prims_ok (.inr (.inr rfl)) (NoSp.of_all (by decide +kernel))

end VG.Proof.MlDsa.X86.Sign
